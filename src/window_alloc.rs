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
// compiled region, trace by trace (see Note [Trace register allocation]):
//
// * Backward, deciding placements. A `Placement` says which slot's current
//   value the code after a point wants in each register. Walking a trace from
//   its end, each window op is placed ([`WindowAlloc::place`]) at the usable
//   `SKIP` that forces the fewest moves and loads after it, at `MEMORY_COST` per
//   load and `MOVE_COST` per move: a move for an output wanted in a register
//   other than its own, and for an input wanted unchanged in another register
//   too. A wanted value in the op's run that the op doesn't leave there is
//   displaced: moved back after the op from a copy that survives it, or from
//   the first free register outside the run, where it waits (a move), or else
//   reloaded after the op. The placement before the op has its inputs at `SKIP
//   + i`, and the displaced values that wait. Ties go to the highest `SKIP`:
//   the use places a value, and its definer, placed later, must put its output
//   there, at the definer's `SKIP` plus the output's index, which for an op
//   with its outputs last is above the definer's inputs. A use placed high
//   leaves its definers room below it; one placed at the bottom of the window
//   wants values where no such definer can write. An inline guard is a read
//   of its slot: the placement before it keeps the slot where it is, or puts
//   it in the first free register.
//
// * Forward, generating code, doing exactly what the backward pass decided.
//   Before each window op, the window is reconciled with the placement planned
//   before it ([`WindowAlloc::reconcile`]): the dirty values it overwrites that
//   survive nowhere else and that the op doesn't rewrite are stored, then its
//   wanted registers are filled as one parallel move (see Note [Parallel
//   moves]). The op then runs at its planned `SKIP` ([`WindowAlloc::op`]).
//   Registers a placement doesn't care about keep their values. Each op's
//   `SKIP` and placement, and each block's entry window, are kept from the
//   backward pass, packed ([`Packed`]). Only `SKIP`s would not do: the forward
//   pass would drop or store what the plan moves aside, and every edge would
//   pay to reconcile the difference.
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

/// A `Placement` in a byte per register, to keep per block: a Lua frame has at
/// most 250 slots, so a slot fits in a byte, with `u8::MAX` for none.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Packed([u8; WINDOW]);

impl Packed {
    pub fn pack(placement: &Placement) -> Packed {
        Packed(placement.map(|slot| match slot {
            None => u8::MAX,
            Some(slot) => u8::try_from(slot).ok().filter(|&byte| byte != u8::MAX).expect("a frame slot below 255"),
        }))
    }

    pub fn unpack(self) -> Placement {
        self.0.map(|byte| (byte != u8::MAX).then_some(byte as usize))
    }
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
        // A slot loaded into several registers is loaded once and copied.
        let mut moves: SmallVec<[(usize, Source); 8]> = SmallVec::new();
        let mut copies: SmallVec<[(usize, usize); WINDOW]> = SmallVec::new();
        for (reg, &slot) in to.regs.iter().enumerate() {
            let Some(slot) = slot else { continue };
            let src = if now.regs[reg] == Some(slot) { Some(reg) } else { now.position(slot) };
            match src {
                Some(src) => moves.push((reg, Source::Reg(src))),
                None => match moves.iter().find(|(_, src)| *src == Source::Memory(slot)) {
                    Some(&(first, _)) => copies.push((reg, first)),
                    None => moves.push((reg, Source::Memory(slot))),
                },
            }
        }
        parallel_move(&mut moves, &mut emits);
        emits.extend(copies.into_iter().map(|(dst, src)| Emit::Move { dst, src }));
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
    /// before it. `None` if there is no usable `SKIP`. See Note [Window
    /// allocation].
    pub fn place(&self, op: &dyn Window, skips: impl IntoIterator<Item = usize>, after: &Placement) -> Option<(usize, Placement)> {
        let slots = op.operands();
        let accesses = op.accesses();
        skips
            .into_iter()
            .filter(|&skip| skip + slots.len() <= self.width)
            .map(|skip| {
                let (cost, before) = self.place_at(slots, accesses, skip, after);
                (cost, skip, before)
            })
            .min_by_key(|&(cost, skip, _)| (cost, std::cmp::Reverse(skip)))
            .map(|(_, skip, before)| (skip, before))
    }

    /// The cost of placing an op at `skip` before `after`, and the placement it
    /// wants before it.
    fn place_at(&self, slots: &[usize], accesses: &[Access], skip: usize, after: &Placement) -> (u32, Placement) {
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
        // A displaced value is moved back after the op from a copy that survives
        // it, or from a free register outside the run where it waits, or else
        // reloaded after the op.
        for slot in displaced {
            if before.contains(&Some(slot)) {
                cost += MOVE_COST;
            } else if let Some(reg) = (0..self.width).rev().find(|reg| !run.contains(reg) && before[*reg].is_none()) {
                before[reg] = Some(slot);
                cost += MOVE_COST;
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
    /// version.
    #[derive(Debug, Default)]
    struct Machine {
        memory: HashMap<usize, u32>,
        current: HashMap<usize, u32>,
        regs: [Option<(usize, u32)>; WINDOW + 1],
    }

    impl Machine {
        fn version(map: &HashMap<usize, u32>, slot: usize) -> u32 {
            map.get(&slot).copied().unwrap_or(0)
        }
        fn exec(&mut self, emit: Emit, op: Option<&dyn Window>) {
            match emit {
                Emit::Load { reg, slot } => {
                    self.regs[reg] = Some((slot, Self::version(&self.memory, slot)));
                }
                Emit::Store { slot, reg } => {
                    let current = Self::version(&self.current, slot);
                    assert_eq!(self.regs[reg], Some((slot, current)), "store of a stale value");
                    self.memory.insert(slot, current);
                }
                Emit::Move { dst, src } => {
                    self.regs[dst] = self.regs[src];
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

    /// Allocate a run streaming and execute it in a window of `width` registers.
    fn run(width: usize, ops: &[TestOp]) {
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

    /// Place a run bottom-up, with nothing wanted after it, then execute it as
    /// placed in a window of `width` registers.
    fn run_backward(width: usize, ops: &[TestOp]) {
        let windows = windows(ops);
        let mut alloc = WindowAlloc::with_width(width);
        let mut after: Placement = [None; WINDOW];
        let mut placed = Vec::new();
        for w in windows.iter().rev() {
            let (skip, before) = alloc.place(&**w, 0..WINDOW, &after).unwrap();
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
    fn finish(mut alloc: WindowAlloc, mut machine: Machine, ops: &[TestOp]) {
        for emit in alloc.flush() {
            machine.exec(emit, None);
        }
        assert!(alloc.is_empty());
        for (&slot, &version) in &machine.current {
            assert_eq!(Machine::version(&machine.memory, slot), version, "slot {slot} not flushed in {ops:?}");
        }
    }

    use TestOp::{Bin as B, Get as G, Loop as L, Out as U, Set as S};

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
