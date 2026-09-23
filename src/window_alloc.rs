//! Register allocation for window ops in the JIT: which window register holds
//! which stack slot across a run of `Storage`/`ExecWindow` residuals. See Note
//! [Register window] and Note [Window allocation].

use smallvec::SmallVec;

use crate::window::{Access, Gpr, Window, WINDOW};

// Note [Window allocation]
// ~~~~~~~~~~~~~~~~~~~~~~~~
// A run of window residuals is allocated as a whole. `begin` scans it once
// (backwards) to find, for each op, the next access of each operand's slot later
// in the run. `Storage` only records its token; each op is then placed where it
// is cheapest: for every `SKIP` it fits at, plan the resculpt of `w[SKIP..]` and
// keep the cheapest plan, costing a load or store `MEMORY_COST` and a register
// move `MOVE_COST`:
//
// * an input already in its register costs nothing, one cached in another
//   register a move, and an uncached one a load (a second use of the same slot in
//   the op is a copy of the first);
// * a cached value displaced by the op's run that is read again later in the run
//   moves to a spare register, or is evicted (stored if dirty, then reloaded at
//   its next read) — farthest next read first. A dirty value never read again in
//   the run is stored now instead of at the run's end (the same store either
//   way), and one whose next access is a write is dead and dropped;
// * a spare register holds nothing, a value that is dead after the op, or a copy
//   of a value that is also kept elsewhere.
//
// Plans are ranked by their cost plus the cheapest plan for the next op from the
// window they leave (a one-op lookahead, which e.g. places a result where the
// next op's run won't displace it), then by their own cost and lowest `SKIP`.
// The run's end flushes every dirty register. Planning an op is constant work,
// so allocating a run is linear in its length.

/// Location of a value for [`Emit`]: window register `0..WINDOW`, or `SCRATCH`.
pub const SCRATCH: usize = WINDOW;

const MEMORY_COST: u32 = 4;
const MOVE_COST: u32 = 1;

/// Code the JIT emits for window ops, over [`SCRATCH`] and the window registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Emit {
    /// Load `slot`'s stack home into `reg`.
    Load { reg: usize, slot: usize },
    /// Store `reg` to `slot`'s stack home.
    Store { slot: usize, reg: usize },
    /// Copy `src` to `dst`.
    Move { dst: usize, src: usize },
    /// Run the op with its operands at `w[skip..]`.
    Op { skip: usize },
}

/// A window residual, as the allocator sees it.
pub enum Step<'a> {
    Storage(Gpr, Access),
    Op(&'a dyn Window),
}

/// The next access of a slot, by op index in the run.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Next {
    Read(usize),
    Write(usize),
    Never,
}

/// What the rest of the run does with a slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Later {
    next: Next,
    /// Whether some later op writes the slot, so that its current value, if
    /// stored, is stored again.
    rewritten: bool,
}

impl Later {
    const NEVER: Later = Later { next: Next::Never, rewritten: false };
}

/// An op of the run: its operands' slots (inputs, then outputs) and, for each,
/// what the rest of the run does with the slot.
#[derive(Debug)]
struct OpInfo {
    slots: SmallVec<[usize; WINDOW]>,
    inputs: usize,
    later: SmallVec<[Later; WINDOW]>,
}

impl OpInfo {
    fn later_of(&self, slot: usize) -> Option<Later> {
        self.slots.iter().position(|&s| s == slot).map(|i| self.later[i])
    }
    fn writes(&self, slot: usize) -> bool {
        self.slots[self.inputs..].contains(&slot)
    }
}

/// The window's state between window residuals.
#[derive(Debug, Clone, Default)]
struct State {
    /// The slot whose current value each register holds.
    regs: [Option<usize>; WINDOW],
    /// Cached slots whose current value is only in registers.
    dirty: SmallVec<[usize; WINDOW]>,
    /// What the rest of the run does with each cached slot.
    later: SmallVec<[(usize, Later); WINDOW]>,
}

impl State {
    fn is_dirty(&self, slot: usize) -> bool {
        self.dirty.contains(&slot)
    }
    fn later_of(&self, slot: usize) -> Later {
        self.later.iter().find(|(s, _)| *s == slot).map_or(Later::NEVER, |&(_, later)| later)
    }
    fn position(&self, slot: usize) -> Option<usize> {
        self.regs.iter().position(|&s| s == Some(slot))
    }
}

/// A resculpt of the window for one op at one `SKIP`.
struct Plan {
    skip: usize,
    cost: u32,
    emits: SmallVec<[Emit; 16]>,
    after: State,
}

/// Allocates the window registers of a run of window residuals. See Note
/// [Window allocation].
#[derive(Debug, Default)]
pub struct WindowAlloc {
    state: State,
    /// Tokens recorded by `Storage` since the last op.
    pending: SmallVec<[(Gpr, Access); WINDOW]>,
    run: Vec<OpInfo>,
    /// Index in `run` of the next op.
    op: usize,
}

impl WindowAlloc {
    /// Start a run of window residuals.
    pub fn begin<'a>(&mut self, run: impl IntoIterator<Item = Step<'a>>) {
        assert!(self.is_empty(), "a window run began before the last one was flushed");
        self.run.clear();
        self.op = 0;
        for step in run {
            if let Step::Op(op) = step {
                self.run.push(OpInfo {
                    slots: op.operands().iter().map(|gpr| gpr.slot()).collect(),
                    inputs: op.inputs(),
                    later: SmallVec::new(),
                });
            }
        }
        let mut later: SmallVec<[(usize, Later); 16]> = SmallVec::new();
        for (k, info) in self.run.iter_mut().enumerate().rev() {
            info.later = info
                .slots
                .iter()
                .map(|slot| later.iter().find(|(s, _)| s == slot).map_or(Later::NEVER, |&(_, later)| later))
                .collect();
            for &slot in &info.slots {
                let access = if info.slots[..info.inputs].contains(&slot) { Next::Read(k) } else { Next::Write(k) };
                let rewritten = info.writes(slot);
                match later.iter_mut().find(|(s, _)| *s == slot) {
                    Some((_, entry)) => *entry = Later { next: access, rewritten: entry.rewritten || rewritten },
                    None => later.push((slot, Later { next: access, rewritten })),
                }
            }
        }
    }

    /// Whether no register holds a value and no token is pending.
    pub fn is_empty(&self) -> bool {
        self.pending.is_empty() && self.state.regs.iter().all(Option::is_none)
    }

    /// A `Storage` of the run.
    pub fn storage(&mut self, gpr: Gpr, access: Access) {
        self.pending.push((gpr, access));
    }

    /// The next op of the run: resculpt the window for it at the cheapest of
    /// `skips`, and run it. `None` if `skips` is empty.
    pub fn op(&mut self, op: &dyn Window, skips: impl IntoIterator<Item = usize>) -> Option<SmallVec<[Emit; 16]>> {
        let name = op.name();
        let operands = op.operands();
        assert_eq!(self.pending.len(), operands.len(), "{name}: operands without a Storage");
        for (i, (&(gpr, access), operand)) in self.pending.iter().zip(operands).enumerate() {
            assert_eq!(gpr, *operand, "{name}: operand {i} is not the token of its Storage");
            let role = if i < op.inputs() { Access::Read } else { Access::Write };
            assert_eq!(access, role, "{name}: operand {i} was stored as {access:?}");
        }
        self.pending.clear();
        let k = self.op;
        self.op += 1;

        let plan = skips
            .into_iter()
            .filter(|&skip| skip + operands.len() <= WINDOW)
            .map(|skip| self.plan(&self.state, k, skip))
            .min_by_key(|plan| (plan.cost + self.best_cost(&plan.after, k + 1), plan.cost, plan.skip))?;
        self.state = plan.after;
        Some(plan.emits)
    }

    /// End the run: flush every dirty register.
    pub fn flush(&mut self) -> SmallVec<[Emit; WINDOW]> {
        assert!(self.pending.is_empty(), "a window run ended between a Storage and its op");
        let state = core::mem::take(&mut self.state);
        state
            .dirty
            .iter()
            .map(|&slot| Emit::Store { slot, reg: state.position(slot).expect("dirty slot in a register") })
            .collect()
    }

    /// The cost of the cheapest plan for op `k` from `state` (0 past the run).
    fn best_cost(&self, state: &State, k: usize) -> u32 {
        let Some(info) = self.run.get(k) else { return 0 };
        (0..=WINDOW - info.slots.len()).map(|skip| self.plan(state, k, skip).cost).min().unwrap_or(0)
    }

    /// Resculpt the window from `now` for op `k` at `skip`.
    fn plan(&self, now: &State, k: usize, skip: usize) -> Plan {
        let info = &self.run[k];
        let span = skip..skip + info.slots.len();
        let inputs = &info.slots[..info.inputs];
        let later_of = |slot: usize| info.later_of(slot).unwrap_or_else(|| now.later_of(slot));
        let next_after = |slot: usize| later_of(slot).next;

        let mut cost = 0;
        let mut emits = SmallVec::new();
        let mut after = now.clone();

        // What happens to each cached value once the op's span is overwritten.
        // Inputs stay cached at their span registers. Of the rest, a value
        // outside the span keeps one register (its other copies are spare); a
        // value only inside the span needs a new home if it is read again.
        let mut keep: SmallVec<[usize; WINDOW]> = SmallVec::new();
        let mut homeless: SmallVec<[(usize, usize); WINDOW]> = SmallVec::new();
        let mut spare: SmallVec<[usize; WINDOW]> = SmallVec::new();
        for reg in 0..WINDOW {
            let Some(slot) = now.regs[reg] else {
                if !span.contains(&reg) {
                    spare.push(reg);
                }
                continue;
            };
            let live = !info.writes(slot) && matches!(next_after(slot), Next::Read(_));
            let flush = now.is_dirty(slot) && next_after(slot) == Next::Never && !info.writes(slot);
            let outside = !span.contains(&reg);
            if inputs.contains(&slot) || !(live || flush) || keep.contains(&slot) {
                if outside {
                    spare.push(reg);
                }
            } else if outside {
                keep.push(slot);
            } else if !homeless.iter().any(|&(s, _)| s == slot) {
                homeless.push((slot, reg));
            }
        }
        // A kept value in a register that is also elsewhere in the span but
        // homeless there is kept, not homeless.
        homeless.retain(|(slot, _)| !keep.contains(slot));
        // Registers outside the span holding a value to store: storing it now
        // is the store the run's end would do, and frees the register.
        let mut stores: SmallVec<[(usize, usize); WINDOW]> = SmallVec::new();
        keep.retain(|&mut slot| {
            let reg = (0..WINDOW).find(|r| !span.contains(r) && now.regs[*r] == Some(slot)).unwrap();
            if matches!(next_after(slot), Next::Read(_)) {
                return true;
            }
            stores.push((slot, reg));
            spare.push(reg);
            false
        });
        // Homeless values that are only to be stored are stored now.
        homeless.retain(|&mut (slot, reg)| {
            if matches!(next_after(slot), Next::Read(_)) {
                return true;
            }
            stores.push((slot, reg));
            false
        });
        // Homes for the rest, costliest to evict first, then soonest next read;
        // the others are evicted. Evicting costs the reload at the next read,
        // and a store if the value is dirty and the slot is written again later
        // (otherwise it is the store the run's end would do anyway).
        let evict_cost = |slot: usize| {
            MEMORY_COST + if now.is_dirty(slot) && later_of(slot).rewritten { MEMORY_COST } else { 0 }
        };
        homeless.sort_by_key(|&(slot, _)| match next_after(slot) {
            Next::Read(at) => (core::cmp::Reverse(evict_cost(slot)), at),
            _ => unreachable!(),
        });
        let mut moves: SmallVec<[(usize, Source); 8]> = SmallVec::new();
        for (i, (slot, reg)) in homeless.into_iter().enumerate() {
            match spare.get(i) {
                Some(&home) => {
                    moves.push((home, Source::Reg(reg)));
                    after.regs[home] = Some(slot);
                    cost += MOVE_COST;
                }
                None => {
                    if now.is_dirty(slot) {
                        stores.push((slot, reg));
                    }
                    cost += evict_cost(slot);
                }
            }
        }
        for &(slot, reg) in &stores {
            emits.push(Emit::Store { slot, reg });
            after.dirty.retain(|s| *s != slot);
        }

        // Inputs into the span: from a register caching the slot, else loaded;
        // a repeated input is a copy of its first use.
        let mut copies: SmallVec<[(usize, usize); WINDOW]> = SmallVec::new();
        for (i, &slot) in inputs.iter().enumerate() {
            let reg = skip + i;
            if let Some(first) = inputs[..i].iter().position(|&s| s == slot) {
                if now.regs[reg] != Some(slot) {
                    copies.push((reg, skip + first));
                    cost += MOVE_COST;
                }
            } else if now.regs[reg] != Some(slot) {
                let source = match now.position(slot) {
                    Some(from) => {
                        cost += MOVE_COST;
                        Source::Reg(from)
                    }
                    None => {
                        cost += MEMORY_COST;
                        Source::Memory(slot)
                    }
                };
                moves.push((reg, source));
            }
            after.regs[reg] = Some(slot);
        }
        cost += MOVE_COST * sequentialize(&mut moves, &mut emits);
        emits.extend(copies.into_iter().map(|(dst, src)| Emit::Move { dst, src }));
        emits.push(Emit::Op { skip });

        // Outputs replace every older copy of their slots.
        for (j, &slot) in info.slots[info.inputs..].iter().enumerate() {
            for reg in after.regs.iter_mut().filter(|r| **r == Some(slot)) {
                *reg = None;
            }
            after.regs[skip + info.inputs + j] = Some(slot);
            if !after.dirty.contains(&slot) {
                after.dirty.push(slot);
            }
        }
        // Anything no longer cached drops its bookkeeping.
        after.dirty.retain(|slot| after.regs.contains(&Some(*slot)));
        for (i, &slot) in info.slots.iter().enumerate() {
            match after.later.iter_mut().find(|(s, _)| *s == slot) {
                Some(entry) => entry.1 = info.later[i],
                None => after.later.push((slot, info.later[i])),
            }
        }
        after.later.retain(|(slot, _)| after.regs.contains(&Some(*slot)));
        Plan { skip, cost, emits, after }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Source {
    Reg(usize),
    Memory(usize),
}

/// Emit the parallel assignment `moves` (distinct destinations) as a sequence,
/// breaking cycles through `SCRATCH`. Returns how many scratch moves it took.
fn sequentialize(moves: &mut SmallVec<[(usize, Source); 8]>, emits: &mut SmallVec<[Emit; 16]>) -> u32 {
    moves.retain(|(dst, src)| *src != Source::Reg(*dst));
    let mut extra = 0;
    while !moves.is_empty() {
        let read = |reg: usize, moves: &[(usize, Source)]| moves.iter().any(|(_, src)| *src == Source::Reg(reg));
        match moves.iter().position(|&(dst, _)| !read(dst, moves)) {
            Some(i) => {
                let (dst, src) = moves.remove(i);
                emits.push(match src {
                    Source::Reg(src) => Emit::Move { dst, src },
                    Source::Memory(slot) => Emit::Load { reg: dst, slot },
                });
            }
            None => {
                // Every destination is still read: a cycle. Park one in SCRATCH.
                let (dst, _) = moves[0];
                emits.push(Emit::Move { dst: SCRATCH, src: dst });
                extra += 1;
                for (_, src) in moves.iter_mut() {
                    if *src == Source::Reg(dst) {
                        *src = Source::Reg(SCRATCH);
                    }
                }
            }
        }
    }
    extra
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lboxed::LBoxed;
    use crate::window::{windowed, Tokens};
    use std::collections::HashMap;

    windowed!(Bin, [], [], |owner, state, base| (a, b) -> (d) {
        *d = LBoxed::from_number(a.as_number().unwrap_unchecked() + b.as_number().unwrap_unchecked());
    });
    windowed!(Un, [], [], |owner, state, base| (a) -> (d) {
        *d = a;
    });

    /// An op of a test run: input slots and an output slot.
    #[derive(Debug, Clone, Copy)]
    enum TestOp {
        Bin(usize, usize, usize),
        Un(usize, usize),
    }

    /// Executes allocator output on symbolic values (slot, version), checking
    /// that every op reads the current version of its inputs, every store writes
    /// a current version, and after the run the stack holds every slot's latest
    /// version; counts the memory accesses and moves.
    #[derive(Debug, Default)]
    struct Machine {
        memory: HashMap<usize, u32>,
        current: HashMap<usize, u32>,
        regs: [Option<(usize, u32)>; WINDOW + 1],
        loads: u32,
        stores: u32,
        moves: u32,
    }

    impl Machine {
        fn version(map: &HashMap<usize, u32>, slot: usize) -> u32 {
            map.get(&slot).copied().unwrap_or(0)
        }
        fn exec(&mut self, emit: Emit, op: Option<(&[usize], usize)>) {
            match emit {
                Emit::Load { reg, slot } => {
                    self.regs[reg] = Some((slot, Self::version(&self.memory, slot)));
                    self.loads += 1;
                }
                Emit::Store { slot, reg } => {
                    let current = Self::version(&self.current, slot);
                    assert_eq!(self.regs[reg], Some((slot, current)), "store of a stale value");
                    self.memory.insert(slot, current);
                    self.stores += 1;
                }
                Emit::Move { dst, src } => {
                    self.regs[dst] = self.regs[src];
                    self.moves += 1;
                }
                Emit::Op { skip } => {
                    let (slots, inputs) = op.expect("an op");
                    for (i, &slot) in slots[..inputs].iter().enumerate() {
                        let current = Self::version(&self.current, slot);
                        assert_eq!(self.regs[skip + i], Some((slot, current)), "input {i} of {slots:?}");
                    }
                    for (j, &slot) in slots[inputs..].iter().enumerate() {
                        let version = Self::version(&self.current, slot) + 1;
                        self.current.insert(slot, version);
                        self.regs[skip + inputs + j] = Some((slot, version));
                    }
                }
            }
        }
    }

    /// Allocate and execute a run, returning the machine for its counts.
    fn run(ops: &[TestOp]) -> Machine {
        let mut tokens = Tokens::default();
        let windows: Vec<Box<dyn Window>> = ops
            .iter()
            .map(|op| -> Box<dyn Window> {
                match *op {
                    TestOp::Bin(a, b, d) => Box::new(Bin::new(&[tokens.mint(a), tokens.mint(b), tokens.mint(d)])),
                    TestOp::Un(a, d) => Box::new(Un::new(&[tokens.mint(a), tokens.mint(d)])),
                }
            })
            .collect();
        fn steps(w: &dyn Window) -> Vec<Step<'_>> {
            let accesses = (0..w.operands().len()).map(|i| if i < w.inputs() { Access::Read } else { Access::Write });
            w.operands().iter().zip(accesses).map(|(g, a)| Step::Storage(*g, a)).chain([Step::Op(w)]).collect()
        }
        let mut alloc = WindowAlloc::default();
        alloc.begin(windows.iter().flat_map(|w| steps(&**w)));
        let mut machine = Machine::default();
        for w in &windows {
            for (i, gpr) in w.operands().iter().enumerate() {
                alloc.storage(*gpr, if i < w.inputs() { Access::Read } else { Access::Write });
            }
            let slots: Vec<usize> = w.operands().iter().map(|g| g.slot()).collect();
            for emit in alloc.op(&**w, 0..WINDOW).unwrap() {
                machine.exec(emit, Some((&slots, w.inputs())));
            }
        }
        for emit in alloc.flush() {
            machine.exec(emit, None);
        }
        assert!(alloc.is_empty());
        for (&slot, &version) in &machine.current {
            assert_eq!(Machine::version(&machine.memory, slot), version, "slot {slot} not flushed in {ops:?}");
        }
        machine
    }

    use TestOp::Bin as B;

    /// nbody `advance`, block 94: `dz = biz - dz; t23 = dx*dx; t24 = dy*dy;
    /// t23 += t24; t24 = dz*dz; t23 += t24` (slots: biz 10, dx 20, dy 21, dz 22).
    /// Worked by hand, a 4-register window does it in 5 loads, 3 stores and 7
    /// moves (the floor is 4 loads and 3 stores: only one register is spare
    /// beside a 3-register op, so dz is evicted once), against 12 loads and 6
    /// stores through the stack.
    #[test]
    fn nbody_dist2() {
        let m = run(&[B(10, 22, 22), B(20, 20, 23), B(21, 21, 24), B(23, 24, 23), B(22, 22, 24), B(23, 24, 23)]);
        assert_eq!((m.loads, m.stores, m.moves), (5, 3, 7), "{m:?}");
    }

    /// nbody `advance`, block 100: `bm = bm * mag; t26 = dx * bm; bivx -= t26;
    /// ...; bm = bimass * mag` (bivx 12, bm 25, mag 24, dx 20, t26 26). Worked
    /// by hand: 10 loads and 5 stores (floor 9 and 5), against 16 and 8; the
    /// allocator needs 6 moves, 2 fewer than the hand plan.
    #[test]
    fn nbody_velocity() {
        let m = run(&[
            B(25, 24, 25),
            B(20, 25, 26),
            B(12, 26, 12),
            B(21, 25, 26),
            B(13, 26, 13),
            B(22, 25, 26),
            B(14, 26, 14),
            B(11, 24, 25),
        ]);
        assert_eq!((m.loads, m.stores, m.moves), (10, 5, 6), "{m:?}");
    }

    /// Every sequence of `len` slots over at most `max` distinct slots, up to
    /// renaming: slots numbered in order of first use.
    fn slot_patterns(len: usize, max: usize) -> Vec<Vec<usize>> {
        fn extend(pattern: &mut Vec<usize>, len: usize, max: usize, out: &mut Vec<Vec<usize>>) {
            if pattern.len() == len {
                out.push(pattern.clone());
                return;
            }
            let fresh = pattern.iter().max().map_or(0, |m| m + 1);
            for slot in 0..=fresh.min(max - 1) {
                pattern.push(slot);
                extend(pattern, len, max, out);
                pattern.pop();
            }
        }
        let mut out = Vec::new();
        extend(&mut Vec::new(), len, max, &mut out);
        out
    }

    /// Every run of three ops, over up to five slots for binary ops alone and
    /// four with unary ones mixed in, is allocated correctly (up to renaming
    /// slots, which the allocator is indifferent to).
    #[test]
    fn exhaustive_small_runs() {
        for shapes in 0..8u32 {
            let arities: Vec<usize> = (0..3).map(|i| if shapes & (1 << i) == 0 { 3 } else { 2 }).collect();
            let max = if shapes == 0 { 5 } else { 4 };
            for pattern in slot_patterns(arities.iter().sum(), max) {
                let mut slots = pattern.into_iter();
                let mut next = || slots.next().unwrap();
                let ops: Vec<TestOp> = arities
                    .iter()
                    .map(|&arity| if arity == 3 { B(next(), next(), next()) } else { TestOp::Un(next(), next()) })
                    .collect();
                run(&ops);
            }
        }
    }

    /// Cycles between registers are broken through `SCRATCH`.
    #[test]
    fn sequentialize_cycle() {
        let mut moves: SmallVec<[(usize, Source); 8]> =
            SmallVec::from_slice(&[(0, Source::Reg(1)), (1, Source::Reg(0)), (2, Source::Memory(7))]);
        let mut emits = SmallVec::new();
        assert_eq!(sequentialize(&mut moves, &mut emits), 1);
        let mut regs = [10, 11, 12, 13, 0];
        for emit in emits {
            match emit {
                Emit::Move { dst, src } => regs[dst] = regs[src],
                Emit::Load { reg, slot } => regs[reg] = slot + 100,
                _ => unreachable!(),
            }
        }
        assert_eq!(regs[..3], [11, 10, 107]);
    }
}
