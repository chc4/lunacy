//! Register allocation for window ops in the JIT: which window register caches
//! which stack slot. Placements are decided bottom-up over a compiled region,
//! then code is generated top-down. See Note [Register window] and Note [Window
//! allocation].

use smallvec::SmallVec;

use crate::window::{Access, Window, WINDOW};

// Note [Window allocation]
// ~~~~~~~~~~~~~~~~~~~~~~~~
// Each register caches at most one slot's current value, and a cached slot is
// dirty while its stack home is stale. Allocation has two passes over a
// compiled region:
//
// * Backward, deciding placements. A `Placement` says which slot's current
//   value the code after a point wants in each register. Walking a block from
//   its end, each window op is placed ([`WindowAlloc::place`]) at the usable
//   `SKIP` that forces the fewest moves and loads after it, at `MEMORY_COST` per
//   load or store and `MOVE_COST` per move: a move for an output wanted in a
//   register other than its own, and for an input wanted unchanged in another
//   register too. A wanted value in the op's run that the op doesn't leave
//   there is displaced: it costs a move if a copy survives the op, and
//   otherwise depends on how the ops above, since the last flush, use its slot
//   ([`Above`]). Unused, it is loaded once wherever that is, so it is dropped
//   for nothing; read or written, it waits in the lowest free register outside
//   the run (a move), or is loaded again after the op (and stored first, if
//   written). The placement before the op has its inputs at `SKIP + i`, and the
//   displaced values that wait. Ties go to the lowest `SKIP`. An inline guard is
//   a read of its slot: the placement before it keeps the slot where it is, or
//   puts it in the lowest free register.
//
// * Forward, generating code. Before each window op, the window is reconciled
//   with the placement before it ([`WindowAlloc::reconcile`]): the dirty values
//   it overwrites that survive nowhere else are stored, then its wanted
//   registers are filled as one parallel move (see Note [Parallel moves]).
//   The op then runs at its `SKIP` ([`WindowAlloc::op`]). Registers a placement
//   doesn't care about keep their values.
//
// Any other residual ends a run of window ops and flushes every dirty
// register, except an inline type guard: it tests the register caching its
// slot, and both its edges carry the window on, the failure edge falling
// through to the residual after it (a thunk, which stores the dirty registers
// before it exits, or a jump). A gas exit stores them too, without ending the
// run ([`WindowAlloc::stores`]).
//
// Jumps carry the window across block edges. Each block is entered with a
// window planned for it (the slots it and its successors read before writing,
// where they read them), and any jump to it transfers the window to that one
// ([`WindowAlloc::transfer`]): dirty values the target doesn't carry dirty are
// stored, then its registers are filled as one parallel move. A block's entry
// window takes its dirty slots from the first jump to it that is compiled. The
// entry stub, for a block entered from the interpreter, loads its window from
// the stack.

// Note [Parallel moves]
// ~~~~~~~~~~~~~~~~~~~~~
// A parallel move fills distinct destination registers all at once, from
// registers or stack homes. Destinations being distinct, each component of its
// location transfer graph is a "windmill": at most one cycle (the axle), with
// trees (the blades) hanging off it (Rideau, Serpette & Leroy, "Tilting at
// windmills with Coq"; https://compiler.club/parallel-moves/). It is
// sequentialized by peeling blades: a move whose destination no remaining move
// reads is emitted and removed, which may free another. When every remaining
// destination is still read only axles are left: one register of a cycle is
// saved to `SCRATCH` and its readers redirected there, turning the cycle into a
// blade. Loads read no register, so they are never on an axle. `SCRATCH` holds
// one value at a time: peeling doesn't stall again until a cycle broken through
// it has peeled completely.

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

/// Window register `reg` (or `SCRATCH`) by name, for dumps.
struct Reg(usize);

impl std::fmt::Display for Reg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            SCRATCH => write!(f, "scratch"),
            reg => write!(f, "w{reg}"),
        }
    }
}

impl std::fmt::Display for Emit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Emit::Load { reg, slot } => write!(f, "{} <- [{slot}]", Reg(reg)),
            Emit::Store { slot, reg } => write!(f, "[{slot}] <- {}", Reg(reg)),
            Emit::Move { dst, src } => write!(f, "{} <- {}", Reg(dst), Reg(src)),
            Emit::Op { skip } => write!(f, "op at w{skip}"),
        }
    }
}

impl Emit {
    fn cost(self) -> u32 {
        match self {
            Emit::Load { .. } | Emit::Store { .. } => MEMORY_COST,
            Emit::Move { .. } => MOVE_COST,
            Emit::Op { .. } => 0,
        }
    }
}

/// The slot whose current value each window register should hold, if any. See
/// Note [Window allocation].
pub type Placement = [Option<usize>; WINDOW];

/// How the window ops before an op, since the last flush, use a slot: what a
/// value of it displaced by the op costs. See Note [Window allocation].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Above {
    /// Neither read nor written, since a flush: loaded once, wherever that is.
    /// (Before a block's first flush, a value can arrive in a register instead,
    /// so there it counts as `Read`.)
    Unused,
    /// Read: loaded for those reads, then again after the op unless it waits
    /// in a register.
    Read,
    /// Written: in a register since, stored and reloaded unless it waits in one.
    Written,
}

/// Which slot each window register caches, and which of them are dirty: the
/// window between residuals, and a block's window on entry.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Cache {
    /// The slot whose current value each register holds.
    regs: [Option<usize>; WINDOW],
    /// Cached slots whose stack home is stale.
    dirty: SmallVec<[usize; WINDOW]>,
}

/// Each register caching a slot, as `w1=[5]`, marked `*` if dirty.
impl std::fmt::Display for Cache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut sep = "";
        write!(f, "{{")?;
        for (reg, slot) in self.regs.iter().enumerate() {
            if let Some(slot) = slot {
                let dirty = if self.dirty.contains(slot) { "*" } else { "" };
                write!(f, "{sep}{}=[{slot}]{dirty}", Reg(reg))?;
                sep = " ";
            }
        }
        write!(f, "}}")
    }
}

impl Cache {
    /// A block's entry window: `regs`, each slot dirty if it is dirty in `from`,
    /// the window of the first jump to the block.
    pub fn entry(regs: Placement, from: &Cache) -> Cache {
        let dirty = from.dirty.iter().filter(|slot| regs.contains(&Some(**slot))).copied().collect();
        Cache { regs, dirty }
    }

    /// The slot each register caches.
    pub fn regs(&self) -> &Placement {
        &self.regs
    }

    fn position(&self, slot: usize) -> Option<usize> {
        self.regs.iter().position(|&s| s == Some(slot))
    }
}

/// An op placed at one `SKIP`: what it emits and the cache it leaves.
struct Plan {
    cost: u32,
    /// Cached values its run overwrites.
    overwritten: usize,
    skip: usize,
    emits: SmallVec<[Emit; 16]>,
    after: Cache,
}

/// Allocates the window registers of a run of window residuals. See Note
/// [Window allocation].
#[derive(Debug)]
pub struct WindowAlloc {
    /// Window registers in use: `WINDOW`, or fewer to test register pressure.
    width: usize,
    cache: Cache,
}

impl Default for WindowAlloc {
    fn default() -> Self {
        Self::with_width(WINDOW)
    }
}

impl WindowAlloc {
    fn with_width(width: usize) -> Self {
        assert!(width <= WINDOW);
        WindowAlloc { width, cache: Cache::default() }
    }

    /// Start a block entered with its window holding `cache`.
    pub fn entering(cache: Cache) -> Self {
        WindowAlloc { cache, ..Self::default() }
    }

    /// What the window holds now.
    pub fn cache(&self) -> &Cache {
        &self.cache
    }

    /// Leave the window's current contents for a block expecting `to`: store
    /// the dirty values `to` doesn't carry dirty, then fill its registers (see
    /// Note [Window allocation]). The window itself is unchanged, for the paths
    /// that don't take this edge.
    pub fn transfer(&self, to: &Cache) -> SmallVec<[Emit; 16]> {
        let now = &self.cache;
        let mut emits: SmallVec<[Emit; 16]> = now
            .dirty
            .iter()
            .filter(|slot| !to.dirty.contains(slot))
            .map(|&slot| Emit::Store { slot, reg: now.position(slot).expect("dirty slot in a register") })
            .collect();
        let mut moves: SmallVec<[(usize, Source); 8]> = to
            .regs
            .iter()
            .enumerate()
            .filter_map(|(reg, &slot)| {
                let slot = slot?;
                let src = if now.regs[reg] == Some(slot) { Some(reg) } else { now.position(slot) };
                Some((reg, src.map_or(Source::Memory(slot), Source::Reg)))
            })
            .collect();
        parallel_move(&mut moves, &mut emits);
        emits
    }

    /// Whether no register holds a value.
    pub fn is_empty(&self) -> bool {
        self.cache.regs.iter().all(Option::is_none)
    }

    /// The next op of the run: resculpt the window for it at the cheapest of the
    /// `skips` it can run at, and run it. `None` if there are none.
    pub fn op(&mut self, op: &dyn Window, skips: impl IntoIterator<Item = usize>) -> Option<SmallVec<[Emit; 16]>> {
        let accesses = op.accesses();
        let slots = op.operands();
        let plan = skips
            .into_iter()
            .filter(|&skip| skip + slots.len() <= self.width)
            .map(|skip| self.plan(&slots, accesses, skip))
            .min_by_key(|plan| (plan.cost, plan.overwritten, plan.skip))?;
        self.cache = plan.after;
        Some(plan.emits)
    }

    /// Place `op` before the placement `after`: the usable `SKIP` from `skips`
    /// forcing the fewest moves and loads after it, and the placement it wants
    /// before it. `above` says how the ops before this one, since the last flush,
    /// use a slot. `None` if there is no usable `SKIP`. See Note [Window
    /// allocation].
    pub fn place(
        &self,
        op: &dyn Window,
        skips: impl IntoIterator<Item = usize>,
        after: &Placement,
        above: impl Fn(usize) -> Above,
    ) -> Option<(usize, Placement)> {
        let slots = op.operands();
        let accesses = op.accesses();
        skips
            .into_iter()
            .filter(|&skip| skip + slots.len() <= self.width)
            .map(|skip| {
                let (cost, before) = self.place_at(slots, accesses, skip, after, &above);
                (cost, skip, before)
            })
            .min_by_key(|&(cost, skip, _)| (cost, skip))
            .map(|(_, skip, before)| (skip, before))
    }

    /// The cost of placing an op at `skip` before `after`, and the placement it
    /// wants before it.
    fn place_at(&self, slots: &[usize], accesses: &[Access], skip: usize, after: &Placement, above: &impl Fn(usize) -> Above) -> (u32, Placement) {
        let run = skip..skip + slots.len();
        let output = |slot: usize| slots.iter().zip(accesses).any(|(&s, &a)| s == slot && a == Access::Write);
        // What a register of the run holds after the op: its output, or its
        // input unless the op rewrites that slot.
        let left = |reg: usize| {
            let i = reg - skip;
            match accesses[i] {
                Access::Write => Some(slots[i]),
                Access::Read => (!output(slots[i])).then_some(slots[i]),
            }
        };
        let mut cost = 0;
        for (reg, want) in after.iter().enumerate() {
            if want.is_some_and(|slot| output(slot)) && !(run.contains(&reg) && left(reg) == *want) {
                cost += MOVE_COST;
            }
        }
        // An input wanted unchanged after the op in a register other than its
        // own must be in both before it: a move.
        for (i, (&slot, &access)) in slots.iter().zip(accesses).enumerate() {
            let elsewhere = (0..self.width).any(|reg| reg != skip + i && after[reg] == Some(slot));
            if access == Access::Read && !output(slot) && elsewhere && after[skip + i] != Some(slot) {
                cost += MOVE_COST;
            }
        }
        // Outputs' old values are dead before the op; the run holds its inputs.
        let mut before = after.map(|want| want.filter(|&slot| !output(slot)));
        let mut displaced: SmallVec<[usize; WINDOW]> = SmallVec::new();
        for reg in run.clone() {
            if let Some(slot) = after[reg].filter(|&slot| !output(slot) && left(reg) != Some(slot)) {
                displaced.push(slot);
            }
            before[reg] = (accesses[reg - skip] == Access::Read).then_some(slots[reg - skip]);
        }
        // A displaced value is moved in after the op from a copy before it, or
        // loaded after the op, which is free for one the ops above don't use.
        // One they use waits in a free register outside the run, or is loaded
        // again (and stored first, if written above).
        for slot in displaced {
            let used = above(slot);
            if before.contains(&Some(slot)) {
                cost += MOVE_COST;
            } else if used == Above::Unused {
            } else if let Some(reg) = (0..self.width).find(|reg| !run.contains(reg) && before[*reg].is_none()) {
                before[reg] = Some(slot);
                cost += MOVE_COST;
            } else if used == Above::Written {
                cost += 2 * MEMORY_COST;
            } else {
                cost += MEMORY_COST;
            }
        }
        (cost, before)
    }

    /// Make the window hold `want` in each register it names, before `op`,
    /// leaving the others as they are: store the dirty values overwritten that
    /// survive nowhere else and that `op` doesn't rewrite, then fill the named
    /// registers as one parallel move (a slot loaded into several registers is
    /// loaded once and copied). See Note [Window allocation].
    pub fn reconcile(&mut self, want: &Placement, op: &dyn Window) -> SmallVec<[Emit; 16]> {
        let rewritten = |slot: usize| op.operands().iter().zip(op.accesses()).any(|(&s, &a)| s == slot && a == Access::Write);
        let now = &self.cache;
        let mut after = now.regs;
        for (reg, slot) in want.iter().enumerate() {
            if slot.is_some() {
                after[reg] = *slot;
            }
        }
        let mut emits: SmallVec<[Emit; 16]> = now
            .dirty
            .iter()
            .filter(|slot| !after.contains(&Some(**slot)) && !rewritten(**slot))
            .map(|&slot| Emit::Store { slot, reg: now.position(slot).expect("dirty slot in a register") })
            .collect();
        let mut moves: SmallVec<[(usize, Source); 8]> = SmallVec::new();
        let mut copies: SmallVec<[(usize, usize); WINDOW]> = SmallVec::new();
        for (reg, &slot) in want.iter().enumerate() {
            let Some(slot) = slot.filter(|&slot| now.regs[reg] != Some(slot)) else { continue };
            match now.position(slot) {
                Some(src) => moves.push((reg, Source::Reg(src))),
                None => match moves.iter().find(|(_, src)| *src == Source::Memory(slot)) {
                    Some(&(first, _)) => copies.push((reg, first)),
                    None => moves.push((reg, Source::Memory(slot))),
                },
            }
        }
        parallel_move(&mut moves, &mut emits);
        emits.extend(copies.into_iter().map(|(dst, src)| Emit::Move { dst, src }));
        let dirty = now.dirty.iter().filter(|slot| after.contains(&Some(**slot))).copied().collect();
        self.cache = Cache { regs: after, dirty };
        emits
    }

    /// A register caching `slot`'s current value, if any.
    pub fn register_of(&self, slot: usize) -> Option<usize> {
        self.cache.position(slot)
    }

    /// The stores that bring every dirty slot's stack home up to date, for a
    /// path leaving the window (the cache itself is kept for the other paths).
    pub fn stores(&self) -> SmallVec<[Emit; WINDOW]> {
        let cache = &self.cache;
        cache
            .dirty
            .iter()
            .map(|&slot| Emit::Store { slot, reg: cache.position(slot).expect("dirty slot in a register") })
            .collect()
    }

    /// End the run: flush every dirty register and empty the window.
    pub fn flush(&mut self) -> SmallVec<[Emit; WINDOW]> {
        let stores = self.stores();
        self.cache = Cache::default();
        stores
    }

    /// Place the op with operand slots `slots` at `skip`.
    fn plan(&self, slots: &[usize], accesses: &[Access], skip: usize) -> Plan {
        let now = &self.cache;
        let span = skip..skip + slots.len();
        let operand = |slot: usize, access: Access| slots.iter().zip(accesses).any(|(&s, &a)| s == slot && a == access);
        let mut emits = SmallVec::new();

        // Values the span overwrites; a dirty one that survives nowhere else is
        // stored first.
        let mut overwritten = 0;
        for (i, reg) in span.clone().enumerate() {
            let Some(slot) = now.regs[reg] else { continue };
            if accesses[i] == Access::Read && slots[i] == slot {
                continue;
            }
            overwritten += 1;
            let elsewhere = (0..self.width).any(|r| !span.contains(&r) && now.regs[r] == Some(slot));
            let survives = elsewhere || operand(slot, Access::Read) || operand(slot, Access::Write);
            let stored = emits.iter().any(|e| matches!(e, Emit::Store { slot: s, .. } if *s == slot));
            if now.dirty.contains(&slot) && !survives && !stored {
                emits.push(Emit::Store { slot, reg });
            }
        }

        // Inputs into the span, as one parallel move; a repeated input copies
        // its first use afterwards.
        let mut moves: SmallVec<[(usize, Source); 8]> = SmallVec::new();
        let mut copies: SmallVec<[(usize, usize); WINDOW]> = SmallVec::new();
        for (i, (&slot, &access)) in slots.iter().zip(accesses).enumerate() {
            let reg = skip + i;
            if access == Access::Write || now.regs[reg] == Some(slot) {
                continue;
            }
            match (0..i).find(|&j| accesses[j] == Access::Read && slots[j] == slot) {
                Some(first) => copies.push((reg, skip + first)),
                None => moves.push((reg, now.position(slot).map_or(Source::Memory(slot), Source::Reg))),
            }
        }
        parallel_move(&mut moves, &mut emits);
        emits.extend(copies.into_iter().map(|(dst, src)| Emit::Move { dst, src }));
        emits.push(Emit::Op { skip });

        // The cache it leaves: inputs in the span, then each output replacing
        // every older copy of its slot.
        let mut after = now.clone();
        for (i, (&slot, &access)) in slots.iter().zip(accesses).enumerate() {
            after.regs[skip + i] = (access == Access::Read).then_some(slot);
        }
        for (i, (&slot, &access)) in slots.iter().zip(accesses).enumerate() {
            if access == Access::Write {
                for reg in after.regs.iter_mut().filter(|r| **r == Some(slot)) {
                    *reg = None;
                }
                after.regs[skip + i] = Some(slot);
                if !after.dirty.contains(&slot) {
                    after.dirty.push(slot);
                }
            }
        }
        for emit in &emits {
            if let Emit::Store { slot, .. } = emit {
                after.dirty.retain(|s| s != slot);
            }
        }
        for slot in &after.dirty {
            assert!(after.regs.contains(&Some(*slot)), "dirty slot {slot} dropped without a store");
        }
        let cost = emits.iter().map(|&emit| emit.cost()).sum();
        Plan { cost, overwritten, skip, emits, after }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Source {
    Reg(usize),
    Memory(usize),
}

/// Emit the parallel move `moves` (distinct destinations) as a sequence of
/// moves and loads. See Note [Parallel moves].
fn parallel_move(moves: &mut SmallVec<[(usize, Source); 8]>, emits: &mut SmallVec<[Emit; 16]>) {
    moves.retain(|(dst, src)| *src != Source::Reg(*dst));
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
                // Every destination is still read: an axle. Save one in SCRATCH.
                let (dst, _) = moves[0];
                emits.push(Emit::Move { dst: SCRATCH, src: dst });
                for (_, src) in moves.iter_mut() {
                    if *src == Source::Reg(dst) {
                        *src = Source::Reg(SCRATCH);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lboxed::LBoxed;
    use crate::window::windowed;
    use std::collections::HashMap;

    // Ops of each shape, their operands in window order as the emit sites
    // declare them, and one with its output first.
    windowed!(Bin, [], [], |owner, state, base| (a, b, out d) {
        *d = LBoxed::from_number(a.as_number().unwrap_unchecked() + b.as_number().unwrap_unchecked());
    });
    windowed!(BinFirst, [], [], |owner, state, base| (out d, a, b) {
        *d = LBoxed::from_number(a.as_number().unwrap_unchecked() + b.as_number().unwrap_unchecked());
    });
    windowed!(Get, [], [], |owner, state, base| (a, out d) {
        *d = a;
    });
    windowed!(Set, [], [], |owner, state, base| (a, b) {
        core::hint::black_box((a, b));
    });
    windowed!(Store, [], [], |owner, state, base| (a, b, c) {
        core::hint::black_box((a, b, c));
    });
    windowed!(Out, [], [], |owner, state, base| (out d) {
        *d = LBoxed::NIL;
    });
    windowed!(Loop, [], [], |owner, state, base| (i, l, s, p, out v) {
        *v = i;
        core::hint::black_box((l, s, p));
    });

    /// An op of a test run: its input slots, then its output slot.
    #[derive(Debug, Clone, Copy)]
    enum TestOp {
        /// Arithmetic, `(a, b, out d)`.
        Bin(usize, usize, usize),
        /// Arithmetic declared `(out d, a, b)`.
        BinFirst(usize, usize, usize),
        /// A table get or move, `(a, out d)`.
        Get(usize, usize),
        /// A table set, `(table, value)`.
        Set(usize, usize),
        /// An array set, `(table, key, value)`.
        Store(usize, usize, usize),
        /// An upvalue get or constant load, `(out d)`.
        Out(usize),
        /// A for loop step, `(idx, limit, step, prev, out var)` with `prev` and
        /// `var` the same slot.
        Loop(usize, usize, usize, usize),
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
        fn exec(&mut self, emit: Emit, op: Option<&dyn Window>) {
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
                    let op = op.expect("an op");
                    let operands = op.operands().iter().zip(op.accesses()).enumerate();
                    for (i, (&slot, _)) in operands.clone().filter(|(_, (_, a))| **a == Access::Read) {
                        let current = Self::version(&self.current, slot);
                        assert_eq!(self.regs[skip + i], Some((slot, current)), "input {i} of {op:?}");
                    }
                    for (i, (&slot, _)) in operands.filter(|(_, (_, a))| **a == Access::Write) {
                        let version = Self::version(&self.current, slot) + 1;
                        self.current.insert(slot, version);
                        self.regs[skip + i] = Some((slot, version));
                    }
                }
            }
        }
    }

    /// Allocate and execute a run in a window of `width` registers, returning
    /// the machine for its counts.
    fn windows(ops: &[TestOp]) -> Vec<Box<dyn Window>> {
        ops.iter()
            .map(|op| -> Box<dyn Window> {
                match *op {
                    TestOp::Bin(a, b, d) => Box::new(Bin::new(&[a, b, d])),
                    TestOp::BinFirst(a, b, d) => Box::new(BinFirst::new(&[d, a, b])),
                    TestOp::Get(a, d) => Box::new(Get::new(&[a, d])),
                    TestOp::Set(a, b) => Box::new(Set::new(&[a, b])),
                    TestOp::Store(a, b, c) => Box::new(Store::new(&[a, b, c])),
                    TestOp::Out(d) => Box::new(Out::new(&[d])),
                    TestOp::Loop(i, l, s, v) => Box::new(Loop::new(&[i, l, s, v, v])),
                }
            })
            .collect()
    }

    fn run(width: usize, ops: &[TestOp]) -> Machine {
        let windows = windows(ops);
        let mut alloc = WindowAlloc::with_width(width);
        let mut machine = Machine::default();
        for w in &windows {
            for emit in alloc.op(&**w, 0..WINDOW).unwrap() {
                machine.exec(emit, Some(&**w));
            }
        }
        finish(alloc, machine, ops)
    }

    /// Place a run bottom-up, with nothing wanted after it, then execute it in a
    /// window of `width` registers, returning the machine for its counts.
    fn run_backward(width: usize, ops: &[TestOp]) -> Machine {
        let windows = windows(ops);
        let mut alloc = WindowAlloc::with_width(width);
        let mut after: Placement = [None; WINDOW];
        let mut placed = Vec::new();
        // Per slot, how many of the ops not yet placed read and write it.
        let mut uses: HashMap<(usize, Access), usize> = HashMap::new();
        for w in &windows {
            for (&slot, &access) in w.operands().iter().zip(w.accesses()) {
                *uses.entry((slot, access)).or_default() += 1;
            }
        }
        for w in windows.iter().rev() {
            for (&slot, &access) in w.operands().iter().zip(w.accesses()) {
                *uses.get_mut(&(slot, access)).unwrap() -= 1;
            }
            let count = |slot, access| uses.get(&(slot, access)).copied().unwrap_or(0);
            let above = |slot| match (count(slot, Access::Write), count(slot, Access::Read)) {
                (0, 0) => Above::Unused,
                (0, _) => Above::Read,
                _ => Above::Written,
            };
            let (skip, before) = alloc.place(&**w, 0..WINDOW, &after, above).unwrap();
            placed.push((skip, before));
            after = before;
        }
        let mut machine = Machine::default();
        for (w, (skip, want)) in windows.iter().zip(placed.into_iter().rev()) {
            for emit in alloc.reconcile(&want, &**w) {
                machine.exec(emit, None);
            }
            for emit in alloc.op(&**w, [skip]).unwrap() {
                machine.exec(emit, Some(&**w));
            }
        }
        finish(alloc, machine, ops)
    }

    /// Flush the window and check the stack holds every slot's latest version.
    fn finish(mut alloc: WindowAlloc, mut machine: Machine, ops: &[TestOp]) -> Machine {
        for emit in alloc.flush() {
            machine.exec(emit, None);
        }
        assert!(alloc.is_empty());
        for (&slot, &version) in &machine.current {
            assert_eq!(Machine::version(&machine.memory, slot), version, "slot {slot} not flushed in {ops:?}");
        }
        machine
    }

    use TestOp::{Bin as B, Get as G, Loop as L, Out as U, Set as S};

    /// Every run of more than one window op that nbody's `advance` executes in
    /// its steady state (`just window-runs nbody`), table gets (G) and sets (S),
    /// upvalue gets (U), moves (G's shape) and for loop steps (L) included (slots: dt 2, i 3/5, bi 7, bix..biz 8-10, bimass 11,
    /// bivx..bivz 12-14, j 15/17, bj 19, dx..dz 20-22, dist2 23, mag 24, bm 25,
    /// temporaries 15 and 26-27), with the (loads, stores, moves) the streaming
    /// rule gives, worked by hand. The floor is a load per slot read before it is
    /// written and a store per slot written.
    const NBODY: [(&[TestOp], (u32, u32, u32)); 7] = [
        // bi.vz = bivz; bi.x = bix + dt*bivx; ...; i += step; the loop step: at
        // the floor. Each `dt*bivx` result lands where `bix + _` starts, read
        // in place with bix loaded below it; each store then moves bi beside t;
        // the loop step finds nothing in place (moving i and step, loading
        // limit and the loop variable) and its five registers overwrite t,
        // stored then instead of at the end.
        (
            &[S(7, 14), B(2, 12, 15), B(8, 15, 15), S(7, 15), B(2, 13, 15), B(9, 15, 15), S(7, 15), B(2, 14, 15), B(10, 15, 15), S(7, 15), B(3, 5, 3), L(3, 4, 5, 6)],
            (12, 3, 6),
        ),
        // dx = bix - bj.x: the got value is read in place as the rhs.
        (&[G(19, 20), B(8, 20, 20)], (2, 1, 0)),
        // dz = biz - bj.z; dist2 = dx*dx + dy*dy + dz*dz; then `sqrt(dist2)`'s
        // upvalue get and argument move: the squares' dead inputs sit between
        // the live dz and dist2, so `dy*dy` finds no three registers free of a
        // dirty value and spills dist2 (a store and a reload over the floor).
        (
            &[G(19, 22), B(10, 22, 22), B(20, 20, 23), B(21, 21, 24), B(23, 24, 23), B(22, 22, 24), B(23, 24, 23), U(24), G(23, 25)],
            (5, 5, 5),
        ),
        // bm = bj.mass * mag; bivx -= dx * bm; ...: `dx * bm` reads bm in place
        // over the cached mag, reloaded for `bimass * mag`; bivy is stored
        // early (its one store).
        (&[G(19, 25), B(25, 24, 25), B(20, 25, 26), B(12, 26, 12), B(21, 25, 26), B(13, 26, 13), B(22, 25, 26), B(14, 26, 14), B(11, 24, 25)], (10, 5, 3)),
        // bj.vx = bj.vx + dx * bm: at the floor; bj.vx moves beside the product
        // and the sum beside bj.
        (&[G(19, 26), B(20, 25, 27), B(26, 27, 26), S(19, 26)], (3, 2, 2)),
        // ... and the inner loop's `j += step` and loop step: at the floor; the
        // loop step moves j and step, loading limit and the loop variable.
        (&[G(19, 26), B(22, 25, 27), B(26, 27, 26), S(19, 26), B(15, 17, 15), L(15, 16, 17, 18)], (7, 4, 4)),
        // mag = dt / (mag * dist2): the product is read in place as the rhs.
        (&[B(24, 23, 25), B(2, 25, 24)], (3, 2, 0)),
    ];

    /// The runs of `NBODY` placed bottom-up, with nothing wanted after them:
    /// (loads, stores, moves). About even with streaming, weighting memory 4 to a
    /// move's 1: fewer loads and stores in `dist2` and the loop tail, more moves
    /// where `bi` is stored to from a different register each time. Placing
    /// bottom-up pays off across block edges, which a single run doesn't show.
    const NBODY_BACKWARD: [(u32, u32, u32); 7] = [(12, 3, 11), (2, 1, 0), (4, 4, 8), (9, 6, 5), (3, 2, 2), (7, 4, 3), (3, 2, 1)];

    #[test]
    fn nbody_backward() {
        let wrong: Vec<String> = NBODY
            .iter()
            .zip(NBODY_BACKWARD)
            .filter_map(|((ops, _), want)| {
                let m = run_backward(WINDOW, ops);
                let got = (m.loads, m.stores, m.moves);
                (got != want).then(|| format!("{ops:?}: (loads, stores, moves) {got:?}, want {want:?}"))
            })
            .collect();
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    }

    #[test]
    fn nbody() {
        let wrong: Vec<String> = NBODY
            .iter()
            .filter_map(|(ops, want)| {
                let m = run(WINDOW, ops);
                let got = (m.loads, m.stores, m.moves);
                (got != *want).then(|| format!("{ops:?}: (loads, stores, moves) {got:?}, want {want:?}"))
            })
            .collect();
        assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    }

    /// The allocator places ops by their operands' accesses, not a layout:
    /// declaring the output first allocates the same run just as well.
    #[test]
    fn operand_order() {
        let ops = [TestOp::BinFirst(20, 20, 23), TestOp::BinFirst(21, 21, 24), TestOp::BinFirst(23, 24, 23)];
        let m = run(WINDOW, &ops);
        assert_eq!((m.loads, m.stores), (2, 2), "{m:?}");
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

    /// Every run of two or three ops of every shape with at most eight operands
    /// between them, over up to four slots (up to renaming, which the allocator
    /// is indifferent to), is allocated correctly in 4 registers (or as many as
    /// its widest op), so that the runs overwrite dirty values, both streaming
    /// and bottom-up.
    #[test]
    fn exhaustive_small_runs() {
        let arity = |op: &TestOp| match op {
            TestOp::Bin(..) | TestOp::BinFirst(..) | TestOp::Store(..) => 3,
            TestOp::Get(..) | TestOp::Set(..) => 2,
            TestOp::Out(..) => 1,
            TestOp::Loop(..) => 5,
        };
        let shapes = [B(0, 0, 0), TestOp::BinFirst(0, 0, 0), G(0, 0), S(0, 0), TestOp::Store(0, 0, 0), U(0), L(0, 0, 0, 0)];
        let mut runs: Vec<Vec<TestOp>> = Vec::new();
        for x in shapes {
            for y in shapes {
                if arity(&x) + arity(&y) <= 8 {
                    runs.push(vec![x, y]);
                }
                for z in shapes {
                    if arity(&x) + arity(&y) + arity(&z) <= 8 {
                        runs.push(vec![x, y, z]);
                    }
                }
            }
        }
        for run_shapes in runs {
            for pattern in slot_patterns(run_shapes.iter().map(arity).sum(), 4) {
                let mut slots = pattern.into_iter();
                let mut next = || slots.next().unwrap();
                let ops: Vec<TestOp> = run_shapes
                    .iter()
                    .map(|shape| match shape {
                        TestOp::Bin(..) => B(next(), next(), next()),
                        TestOp::BinFirst(..) => TestOp::BinFirst(next(), next(), next()),
                        TestOp::Get(..) => G(next(), next()),
                        TestOp::Set(..) => S(next(), next()),
                        TestOp::Store(..) => TestOp::Store(next(), next(), next()),
                        TestOp::Out(..) => U(next()),
                        TestOp::Loop(..) => L(next(), next(), next(), next()),
                    })
                    .collect();
                let width = ops.iter().map(arity).max().unwrap().max(4);
                run(width, &ops);
                run_backward(width, &ops);
            }
        }
    }

    /// Every window over three registers and three slots (each register caching
    /// a slot or nothing, each cached slot dirty or not) transfers to every
    /// other: afterwards the target's registers hold their slots' current
    /// values, and every slot it doesn't carry dirty is current on the stack. A
    /// window transfers to itself with no code.
    #[test]
    fn transfer_exhaustive() {
        const REGS: usize = 3;
        const SLOTS: usize = 3;
        let mut caches = Vec::new();
        for code in 0..(SLOTS + 1).pow(REGS as u32) {
            let mut regs = [None; WINDOW];
            let mut digits = code;
            for reg in regs.iter_mut().take(REGS) {
                *reg = (digits % (SLOTS + 1)).checked_sub(1);
                digits /= SLOTS + 1;
            }
            let cached: Vec<usize> = (0..SLOTS).filter(|slot| regs.contains(&Some(*slot))).collect();
            for mask in 0..1u32 << cached.len() {
                let dirty = cached.iter().enumerate().filter(|(i, _)| mask & 1 << i != 0).map(|(_, &slot)| slot).collect();
                caches.push(Cache { regs, dirty });
            }
        }
        for from in &caches {
            for to in &caches {
                let mut machine = Machine::default();
                for &slot in &from.dirty {
                    machine.current.insert(slot, 1);
                }
                for (reg, slot) in from.regs.iter().enumerate() {
                    machine.regs[reg] = slot.map(|slot| (slot, Machine::version(&machine.current, slot)));
                }
                let emits = WindowAlloc::entering(from.clone()).transfer(to);
                assert!(from != to || emits.is_empty(), "{from:?} to itself: {emits:?}");
                for emit in emits {
                    machine.exec(emit, None);
                }
                for (reg, slot) in to.regs.iter().enumerate() {
                    if let Some(slot) = *slot {
                        let current = Machine::version(&machine.current, slot);
                        assert_eq!(machine.regs[reg], Some((slot, current)), "{from:?} to {to:?}: register {reg}");
                    }
                }
                for slot in (0..SLOTS).filter(|slot| !to.dirty.contains(slot)) {
                    let current = Machine::version(&machine.current, slot);
                    assert_eq!(Machine::version(&machine.memory, slot), current, "{from:?} to {to:?}: slot {slot}");
                }
            }
        }
    }

    /// Cycles between registers are broken through `SCRATCH`.
    #[test]
    fn parallel_move_cycle() {
        let mut moves: SmallVec<[(usize, Source); 8]> =
            SmallVec::from_slice(&[(0, Source::Reg(1)), (1, Source::Reg(0)), (2, Source::Memory(7))]);
        let mut emits = SmallVec::new();
        parallel_move(&mut moves, &mut emits);
        assert_eq!(emits.iter().filter(|e| matches!(e, Emit::Move { dst: SCRATCH, .. })).count(), 1);
        let mut regs: [usize; WINDOW + 1] = core::array::from_fn(|r| 10 + r);
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
