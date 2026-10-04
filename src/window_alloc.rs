//! Register allocation for window ops in the JIT: which window register caches
//! which stack slot. Placements are planned over a compiled region, trace by
//! trace, then code is generated doing what they say. See Note [Register window] and Note [Window
//! allocation].

use smallvec::SmallVec;

use crate::trace::Slots;
use crate::window::{Access, Window, WINDOW};

// Note [Window allocation]
// ~~~~~~~~~~~~~~~~~~~~~~~~
// Each register caches at most one slot's current value, and a cached slot is
// dirty while its stack home is stale. Allocation has two passes over a
// compiled region, trace by trace (see Note [Trace register allocation]):
//
// * Planning placements, one trace at a time ([`plan_trace`], Note [Trace
//   allocation]). A `Placement` says which slot's current value the code
//   wants in each register before a window op, and at a block's start (its
//   entry window); each op gets its `SKIP`.
//
// * Generating code, doing exactly what planning decided.
//   Before each window op, the window is reconciled with the placement planned
//   before it ([`WindowAlloc::reconcile`]): the dirty values it overwrites that
//   survive nowhere else and that the op doesn't rewrite are stored, then its
//   wanted registers are filled as one parallel move (see Note [Parallel
//   moves]). The op then runs at its planned `SKIP` ([`WindowAlloc::op`]).
//   Registers a placement doesn't care about keep their values. Each op's
//   `SKIP` and placement, and each block's entry window, are kept from
//   planning, packed ([`Packed`]).
//
// Any other residual ends a run of window ops and flushes every dirty
// register, except an inline type guard: it tests the register caching its
// slot, and both its edges carry the window on, the failure edge falling
// through to the residual after it (a thunk, which stores the dirty registers
// before it exits, or a jump). A gas exit stores them too, without ending the
// run ([`WindowAlloc::stores`]).
//
// Jumps carry the window across block edges. Each block is entered with a
// window planned for it (see Note [Trace allocation]), and any jump to it
// transfers the window to that one ([`WindowAlloc::transfer`]): dirty values
// the target doesn't carry dirty are stored, then its registers are filled as
// one parallel move. A block's entry window has dirty the slots planned dirty
// and those the first jump to it that is compiled brings dirty, except a loop
// header's, which has dirty exactly the slots the loop writes, as its back edge
// brings them: the back edge doesn't store them every iteration, and the jump
// into the loop stores the rest once, rather than the body whenever it drops
// them.
// The entry stub, for a block entered from the interpreter, loads its window
// from the stack.

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

// Note [Unboxed doubles]
// ~~~~~~~~~~~~~~~~~~~~~~
// Each window register is a pair: its general register, which holds a value
// boxed, and the XMM register of the same index, which holds a double unboxed.
// A cached value is in one of the two, its register's form. A window op takes
// and gives each operand in one form (`Window::doubles`): allocation brings a
// value into the form its op wants as it moves it into the op's run, unboxing
// or boxing it on the way. Nothing outside the JIT knows a value is unboxed: on
// the stack, and to every residual, values are boxed, so every edge leaving
// the window (a store, a flush, a snapshot's stores) boxes what it stores.
//
// A block's entry window has each value in the form its next read in the
// trace wants: the edge into the block converts it once, rather than the code
// it enters each time that runs. So a loop's header has the doubles the loop
// computes unboxed, as its back edge brings them.

/// A window register's index for [`Emit`]: `0..WINDOW`, or `SCRATCH`.
pub const SCRATCH: usize = WINDOW;

/// Half of a window register (or of `SCRATCH`): its general register, holding
/// a value boxed, or if `unboxed` its paired XMM register, holding a double
/// unboxed. See Note [Unboxed doubles].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Loc {
    pub reg: usize,
    pub unboxed: bool,
}

/// Window registers the JIT allocates: the first `ALLOCATED` of the `WINDOW` a
/// stencil passes on. The rest are passed through every op untouched.
pub const ALLOCATED: usize = WINDOW;
const _: () = assert!(ALLOCATED <= WINDOW);

const MEMORY_COST: u32 = 4;
const MOVE_COST: u32 = 1;
/// A move between a register's halves, boxing or unboxing on the way.
const CONVERT_COST: u32 = 2;

/// Code the JIT emits for window ops, over [`SCRATCH`] and the window registers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Emit {
    /// Load `slot`'s stack home into `reg`, unboxing it into its XMM half if
    /// `unboxed`.
    Load { reg: usize, slot: usize, unboxed: bool },
    /// Store `reg` to `slot`'s stack home, boxing it from its XMM half if
    /// `unboxed`.
    Store { slot: usize, reg: usize, unboxed: bool },
    /// Copy `src` to `dst`, boxing or unboxing it if their halves differ.
    Move { dst: Loc, src: Loc },
    /// Run the op with its operands at `w[skip..]`.
    Op { skip: usize },
}

/// A register half by name, for dumps: `w3` boxed, `x3` unboxed.
impl std::fmt::Display for Loc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (self.reg, self.unboxed) {
            (SCRATCH, false) => write!(f, "scratch"),
            (SCRATCH, true) => write!(f, "xscratch"),
            (reg, false) => write!(f, "w{reg}"),
            (reg, true) => write!(f, "x{reg}"),
        }
    }
}

impl std::fmt::Display for Emit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Emit::Load { reg, slot, unboxed } => write!(f, "{} <- [{slot}]", Loc { reg, unboxed }),
            Emit::Store { slot, reg, unboxed } => write!(f, "[{slot}] <- {}", Loc { reg, unboxed }),
            Emit::Move { dst, src } => write!(f, "{dst} <- {src}"),
            Emit::Op { skip } => write!(f, "op at w{skip}"),
        }
    }
}

impl Emit {
    fn cost(self) -> u32 {
        match self {
            Emit::Load { .. } | Emit::Store { .. } => MEMORY_COST,
            Emit::Move { dst, src } if dst.unboxed != src.unboxed => CONVERT_COST,
            Emit::Move { .. } => MOVE_COST,
            Emit::Op { .. } => 0,
        }
    }
}

/// Whether bit `i` of `mask` is set: register or operand `i` unboxed.
fn bit(mask: u8, i: usize) -> bool {
    mask & 1 << i != 0
}

/// The registers `regs` names a slot for, a bit each.
fn occupied(regs: &Placement) -> u8 {
    (0..WINDOW).filter(|&reg| regs[reg].is_some()).fold(0, |mask, reg| mask | 1 << reg)
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
    /// The registers holding theirs unboxed, bit `reg` for register `reg`: only
    /// registers holding a value. See Note [Unboxed doubles].
    unboxed: u8,
    /// Cached slots whose stack home is stale.
    dirty: SmallVec<[usize; WINDOW]>,
}

/// Each register caching a slot, as `w1=[5]` (or `x1=[5]` unboxed), marked `*`
/// if dirty.
impl std::fmt::Display for Cache {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut sep = "";
        write!(f, "{{")?;
        for (reg, slot) in self.regs.iter().enumerate() {
            if let Some(slot) = slot {
                let dirty = if self.dirty.contains(slot) { "*" } else { "" };
                write!(f, "{sep}{}=[{slot}]{dirty}", self.loc(reg))?;
                sep = " ";
            }
        }
        write!(f, "}}")
    }
}

impl Cache {
    /// A block's entry window: `regs`, those of `unboxed` unboxed, each slot
    /// dirty if it is dirty in `from`, the window of the first jump to the
    /// block, or planned dirty in `dirty`. A clean value marked dirty is only
    /// stored again, so any slot can be.
    pub fn entry(regs: Placement, unboxed: u8, from: &Cache, dirty: &Slots) -> Cache {
        let mut dirty: SmallVec<[usize; WINDOW]> = regs.iter().flatten().copied().filter(|slot| from.dirty.contains(slot) || dirty.contains(*slot)).collect();
        dirty.sort_unstable();
        dirty.dedup();
        Cache { regs, unboxed: unboxed & occupied(&regs), dirty }
    }

    /// The slot each register caches.
    pub fn regs(&self) -> &Placement {
        &self.regs
    }

    /// The registers holding theirs unboxed.
    pub fn unboxed(&self) -> u8 {
        self.unboxed
    }

    /// The half of `reg` holding its value.
    pub fn loc(&self, reg: usize) -> Loc {
        Loc { reg, unboxed: bit(self.unboxed, reg) }
    }

    fn position(&self, slot: usize) -> Option<usize> {
        self.regs.iter().position(|&s| s == Some(slot))
    }

    /// A register caching `slot`, one in the form `unboxed` says if any is.
    fn source(&self, slot: usize, unboxed: bool) -> Option<Loc> {
        let regs = || (0..WINDOW).filter(|&reg| self.regs[reg] == Some(slot));
        regs().find(|&reg| bit(self.unboxed, reg) == unboxed).or_else(|| regs().next()).map(|reg| self.loc(reg))
    }

    /// Whether `reg` holds `slot` in the form `unboxed` says.
    fn holds(&self, reg: usize, slot: usize, unboxed: bool) -> bool {
        self.regs[reg] == Some(slot) && bit(self.unboxed, reg) == unboxed
    }

    /// The store bringing dirty `slot`'s stack home up to date.
    fn store(&self, slot: usize) -> Emit {
        let reg = self.position(slot).expect("dirty slot in a register");
        Emit::Store { slot, reg, unboxed: bit(self.unboxed, reg) }
    }

    /// Set `reg` to hold `slot`, if any, in the form `unboxed` says.
    fn set(&mut self, reg: usize, slot: Option<usize>, unboxed: bool) {
        self.regs[reg] = slot;
        self.unboxed = (self.unboxed & !(1 << reg)) | (u8::from(unboxed && slot.is_some()) << reg);
    }

    /// Each slot it caches, once, in the first register caching it.
    fn slots(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        (0..WINDOW).filter_map(|reg| self.regs[reg].filter(|&slot| self.position(slot) == Some(reg)).map(|slot| (reg, slot)))
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
    /// Window registers in use: `ALLOCATED`, or fewer to test register pressure.
    width: usize,
    cache: Cache,
}

impl Default for WindowAlloc {
    fn default() -> Self {
        Self::with_width(ALLOCATED)
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
            .map(|&slot| now.store(slot))
            .collect();
        let mut moves: SmallVec<[(Loc, Source); 8]> = SmallVec::new();
        let mut copies: SmallVec<[(Loc, Loc); WINDOW]> = SmallVec::new();
        for (reg, &slot) in to.regs.iter().enumerate() {
            let Some(slot) = slot else { continue };
            let dst = to.loc(reg);
            let src = if now.regs[reg] == Some(slot) { Some(now.loc(reg)) } else { now.source(slot, dst.unboxed) };
            fill(&mut moves, &mut copies, dst, slot, src);
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
            .map(|skip| self.plan(&slots, accesses, op.doubles(), skip))
            .min_by_key(|plan| (plan.cost, plan.overwritten, plan.skip))?;
        self.cache = plan.after;
        Some(plan.emits)
    }

    /// Make the window hold `want` in each register it names, before `op`,
    /// leaving the others as they are: store the dirty values overwritten that
    /// survive nowhere else and that `op` doesn't rewrite, then fill the named
    /// registers as one parallel move (a slot loaded into several registers is
    /// loaded once and copied). See Note [Window allocation].
    pub fn reconcile(&mut self, want: &Placement, op: &dyn Window, skip: usize) -> SmallVec<[Emit; 16]> {
        let rewritten = |slot: usize| op.operands().iter().zip(op.accesses()).any(|(&s, &a)| s == slot && a.writes());
        let now = &self.cache;
        // Each wanted value in the form its op reads it in, if in its run, else
        // in the one it has.
        let form = |reg: usize, slot: usize| match reg.checked_sub(skip).filter(|&i| i < op.arity() && op.accesses()[i].reads()) {
            Some(i) => bit(op.doubles(), i),
            None if now.regs[reg] == Some(slot) => bit(now.unboxed, reg),
            None => now.source(slot, false).is_some_and(|src| src.unboxed),
        };
        let mut after = now.clone();
        for (reg, slot) in want.iter().enumerate() {
            if let Some(slot) = *slot {
                after.set(reg, Some(slot), form(reg, slot));
            }
        }
        let mut emits: SmallVec<[Emit; 16]> = now
            .dirty
            .iter()
            .filter(|slot| !after.regs.contains(&Some(**slot)) && !rewritten(**slot))
            .map(|&slot| now.store(slot))
            .collect();
        let mut moves: SmallVec<[(Loc, Source); 8]> = SmallVec::new();
        let mut copies: SmallVec<[(Loc, Loc); WINDOW]> = SmallVec::new();
        for (reg, &slot) in want.iter().enumerate() {
            let Some(slot) = slot else { continue };
            let dst = after.loc(reg);
            if now.holds(reg, slot, dst.unboxed) {
                continue;
            }
            fill(&mut moves, &mut copies, dst, slot, now.source(slot, dst.unboxed));
        }
        parallel_move(&mut moves, &mut emits);
        emits.extend(copies.into_iter().map(|(dst, src)| Emit::Move { dst, src }));
        after.dirty.retain(|slot| after.regs.contains(&Some(*slot)));
        self.cache = after;
        emits
    }

    /// A register caching `slot`'s current value, if any.
    pub fn register_of(&self, slot: usize) -> Option<usize> {
        self.cache.position(slot)
    }

    /// The stores that bring every dirty slot's stack home up to date, for a
    /// path leaving the window (the cache itself is kept for the other paths).
    pub fn stores(&self) -> SmallVec<[Emit; WINDOW]> {
        self.cache.dirty.iter().map(|&slot| self.cache.store(slot)).collect()
    }

    /// End the run: flush every dirty register and empty the window.
    pub fn flush(&mut self) -> SmallVec<[Emit; WINDOW]> {
        let stores = self.stores();
        self.cache = Cache::default();
        stores
    }

    /// Place the op with operand slots `slots` at `skip`.
    fn plan(&self, slots: &[usize], accesses: &[Access], doubles: u8, skip: usize) -> Plan {
        let now = &self.cache;
        let span = skip..skip + slots.len();
        let mut emits = SmallVec::new();

        // Values the span overwrites; a dirty one that survives nowhere else is
        // stored first.
        let mut overwritten = 0;
        for (i, reg) in span.clone().enumerate() {
            let Some(slot) = now.regs[reg] else { continue };
            if accesses[i].reads() && slots[i] == slot {
                continue;
            }
            overwritten += 1;
            let elsewhere = (0..self.width).any(|r| !span.contains(&r) && now.regs[r] == Some(slot));
            let survives = elsewhere || slots.contains(&slot);
            let stored = emits.iter().any(|e| matches!(e, Emit::Store { slot: s, .. } if *s == slot));
            if now.dirty.contains(&slot) && !survives && !stored {
                emits.push(Emit::Store { slot, reg, unboxed: bit(now.unboxed, reg) });
            }
        }

        // Inputs into the span in the forms the op takes them, as one parallel
        // move; a repeated input copies its first use afterwards.
        let mut moves: SmallVec<[(Loc, Source); 8]> = SmallVec::new();
        let mut copies: SmallVec<[(Loc, Loc); WINDOW]> = SmallVec::new();
        for (i, (&slot, &access)) in slots.iter().zip(accesses).enumerate() {
            let dst = Loc { reg: skip + i, unboxed: bit(doubles, i) };
            if access == Access::Write || now.holds(dst.reg, slot, dst.unboxed) {
                continue;
            }
            match (0..i).find(|&j| accesses[j].reads() && slots[j] == slot) {
                Some(first) => copies.push((dst, Loc { reg: skip + first, unboxed: bit(doubles, first) })),
                None => moves.push((dst, now.source(slot, dst.unboxed).map_or(Source::Memory(slot), Source::Reg))),
            }
        }
        parallel_move(&mut moves, &mut emits);
        emits.extend(copies.into_iter().map(|(dst, src)| Emit::Move { dst, src }));
        emits.push(Emit::Op { skip });

        // The cache it leaves: inputs in the span, then each output replacing
        // every older copy of its slot, each in its form.
        let mut after = now.clone();
        for (i, (&slot, &access)) in slots.iter().zip(accesses).enumerate() {
            after.set(skip + i, (access == Access::Read).then_some(slot), bit(doubles, i));
        }
        for (i, (&slot, &access)) in slots.iter().zip(accesses).enumerate() {
            if access.writes() {
                for reg in 0..WINDOW {
                    if after.regs[reg] == Some(slot) {
                        after.set(reg, None, false);
                    }
                }
                after.set(skip + i, Some(slot), bit(doubles, i));
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

// Note [Trace allocation]
// ~~~~~~~~~~~~~~~~~~~~~~~
// A trace is planned by one forward pass over its steps, running a
// `WindowAlloc` exactly as code generation will, so the window the plan
// expects at each step is the one the code has. What it minimizes is the
// loads and stores on the trace; moves between registers are close to free
// (docs/trace-register-allocation.md).
//
// A value is worth its register until its next beneficial event: a read,
// which keeping it saves a load, or, while it is dirty, an overwrite, which
// keeping it saves a store. A flush ends every value's worth. An edge leaving
// the trace reads what its target does first (the thesis's pseudo-uses): the
// trace's own continuation, and a jump back to a block of the trace, read
// their target's entry window as the trace's ops read their operands. A value
// with no such event is still worth a register, after every value that has
// one, while it is live along a side exit into a block that has run: the
// exit's own trace starts from the window it leaves. At each window op the
// window keeps the op's operands in its run and as many other values as fit
// outside the run, those with the nearest next events first (Belady); the op
// runs at the `SKIP` needing the fewest moves. A value not kept stays where
// it is, unnamed, until something needs its register.
//
// A block's entry window is the window the trace reaches it with, less the
// values of no further worth. The trace's head starts from a hint, as the
// thesis's inter-trace hints: the window an edge from a trace planned earlier
// leaves into it, or the window of a thunk linked into the region's entry.
//
// A trace none of whose steps touches the window, a block of only a thunk or
// only jumps, is the thesis's trivial trace: its blocks are entered with the
// hint as it is, dirty slots and all, and its exits leave it. So a thunk keeps
// the window of the edge into it, for the code compiled once it is forced to
// start from. (The thesis forwards only the values live into the block; what a
// forced thunk's code reads isn't known, so the whole window is forwarded.)
//
// Loads and stores belong where they run least (the thesis's spill and split
// positions, in the least frequent block), and every edge into a block pays
// for its entry window. So where the edge into a block enters more frequent
// code, the block's entry window holds only values live into it that the
// code it enters reads: those the trace brings, and those with events that
// pay, loaded on that edge rather than in the code it enters. It has dirty
// only the slots that code writes, which its own edges into the block bring
// dirty: any other value dirty on the way in is stored on that edge once,
// rather than by the more frequent code whenever it drops it.

/// A step of a trace, for [`plan_trace`]: its blocks' residuals, as planning
/// sees them.
pub enum Step<'a> {
    /// A block's start, continuing the trace from the step before it, with
    /// its `Rise` if the edge into it enters more frequent code.
    Start(Option<Rise>),
    /// A window op, and the `SKIP`s it can run at.
    Op(&'a dyn Window, SmallVec<[usize; WINDOW]>),
    /// An inline guard testing `slot` in its register, if the window has one.
    Read(usize),
    /// A residual that flushes the window.
    Flush,
    /// A jump to the block starting at step `start`, earlier in the trace:
    /// an edge into it, reading its entry window.
    Back(usize),
    /// An edge leaving the trace into a block `reads` are live into, or that
    /// is entered with them: the trace's own continuation if `hot`, else a
    /// side exit (with none, into a block that never ran).
    Exit { hot: bool, reads: Slots },
}

/// An edge into more frequent code than it leaves: the slots live into the
/// block it enters that the more frequent code reads, and those that code
/// writes. See Note [Trace allocation].
pub struct Rise {
    pub reads: Slots,
    pub writes: Slots,
}

/// A planned trace. See Note [Trace allocation].
pub struct TracePlan {
    /// Per step: at a block's start its entry window, before an op the window
    /// the op wants.
    pub windows: Vec<Placement>,
    pub skips: Vec<usize>,
    /// Per block start, the registers its entry window has unboxed.
    pub unboxed: Vec<u8>,
    /// Per block start, the slots its entry window has dirty.
    pub dirty: Vec<Slots>,
    /// Per `Exit`, the window the trace leaves along it.
    pub exits: Vec<Option<Cache>>,
    /// Whether it is a trivial trace, its blocks entered with the hint as it is.
    pub trivial: bool,
}

/// What lies ahead of each step of a trace, for the worth of keeping a value.
/// See Note [Trace allocation].
struct Ahead {
    /// Per slot, the steps reading (`true`) or writing it, in order.
    events: Vec<Vec<(usize, bool)>>,
    /// Per slot, the steps reading it in a form, unboxed or not, in order.
    forms: Vec<Vec<(usize, bool)>>,
    /// Per slot, the side exits it is live along, in order.
    leaves: Vec<Vec<usize>>,
    flushes: Vec<usize>,
    /// Each jump back into the trace, `(back, start)`.
    backs: Vec<(usize, usize)>,
}

impl Ahead {
    fn new(steps: &[Step]) -> Ahead {
        let mut ahead = Ahead { events: vec![Vec::new(); 256], forms: vec![Vec::new(); 256], leaves: vec![Vec::new(); 256], flushes: Vec::new(), backs: Vec::new() };
        for (step, s) in steps.iter().enumerate() {
            match s {
                Step::Op(op, _) => {
                    for (i, (&slot, &access)) in op.operands().iter().zip(op.accesses()).enumerate() {
                        if access.reads() {
                            ahead.events[slot].push((step, true));
                            ahead.forms[slot].push((step, bit(op.doubles(), i)));
                        }
                        if access.writes() {
                            ahead.events[slot].push((step, false));
                        }
                    }
                }
                Step::Read(slot) => ahead.events[*slot].push((step, true)),
                Step::Exit { hot: true, reads } => reads.iter().for_each(|slot| ahead.events[slot].push((step, true))),
                Step::Exit { hot: false, reads } => reads.iter().for_each(|slot| ahead.leaves[slot].push(step)),
                Step::Flush => ahead.flushes.push(step),
                Step::Back(start) => ahead.backs.push((step, *start)),
                Step::Start(_) => {}
            }
        }
        ahead
    }

    /// The block starting at step `start` is entered with `window`, `unboxed`
    /// its registers holding theirs unboxed: each jump back to it reads that.
    fn entered(&mut self, start: usize, window: &Placement, unboxed: u8) {
        for &(back, _) in self.backs.iter().filter(|&&(_, s)| s == start) {
            for (reg, &slot) in window.iter().enumerate() {
                let Some(slot) = slot else { continue };
                let events = &mut self.events[slot];
                events.insert(events.partition_point(|e| e.0 < back), (back, true));
                let forms = &mut self.forms[slot];
                forms.insert(forms.partition_point(|f| f.0 < back), (back, bit(unboxed, reg)));
            }
        }
    }

    /// The form `slot`'s next read after step `at` takes its current value in,
    /// unboxed or not, if one does before the slot is written or flushed. See
    /// Note [Unboxed doubles].
    fn next_form(&self, slot: usize, at: usize) -> Option<bool> {
        let forms = &self.forms[slot];
        let &(step, unboxed) = forms.get(forms.partition_point(|f| f.0 <= at))?;
        let events = &self.events[slot];
        let written = events[events.partition_point(|e| e.0 <= at)..].iter().find(|e| !e.1).map(|e| e.0);
        let flush = self.flushes.get(self.flushes.partition_point(|&f| f <= at)).copied();
        (written.is_none_or(|w| w >= step) && flush.is_none_or(|f| f > step)).then_some(unboxed)
    }

    /// The worth of keeping `slot` in a register after step `at`, `dirty` or
    /// not, if it has any, least first: how far off its next event that pays
    /// is, or failing one (`true`), the next side exit it is live along.
    fn worth(&self, slot: usize, at: usize, dirty: bool) -> Option<(bool, usize)> {
        if let Some(far) = self.pays(slot, at, dirty) {
            return Some((false, far));
        }
        // Live until its slot is next written, or a flush.
        let written = self.events[slot].get(self.events[slot].partition_point(|e| e.0 <= at)).map(|e| e.0);
        let flushed = self.flushes.get(self.flushes.partition_point(|&f| f <= at)).copied();
        let until = written.into_iter().chain(flushed).min().unwrap_or(usize::MAX);
        let leaves = &self.leaves[slot];
        let leave = leaves.get(leaves.partition_point(|&l| l <= at)).copied().filter(|&l| l < until)?;
        Some((true, leave - at))
    }

    /// How far after step `at` keeping `slot` in a register next pays off,
    /// `dirty` or not, if it does: its next event, unless a flush comes first,
    /// if that is a read, or an overwrite of a dirty value.
    fn pays(&self, slot: usize, at: usize, dirty: bool) -> Option<usize> {
        let events = &self.events[slot];
        let &(step, read) = events.get(events.partition_point(|e| e.0 <= at))?;
        let flush = self.flushes.get(self.flushes.partition_point(|&f| f <= at)).copied();
        (flush.is_none_or(|flush| flush > step) && (read || dirty)).then_some(step - at)
    }
}

/// Each value `cache` holds and its worth after step `at` (see `Ahead::worth`),
/// as `slot:distance`, `slot:exit distance` for one live only along a side
/// exit, or `slot:-` for none, for the trace (`alloc` events).
#[cfg(feature = "tracing")]
fn worths(ahead: &Ahead, cache: &Cache, at: usize) -> String {
    cache
        .slots()
        .map(|(_, slot)| match ahead.worth(slot, at, cache.dirty.contains(&slot)) {
            Some((false, far)) => format!("{slot}:{far}"),
            Some((true, far)) => format!("{slot}:exit {far}"),
            None => format!("{slot}:-"),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// Plan a trace's window ops in a window of `width` registers, its head
/// entered from `hint`; `trace` names it in the trace (`alloc` events, see
/// `just trace-sql`). See Note [Trace allocation].
pub fn plan_trace(steps: &[Step], width: usize, hint: &Cache, trace: u64) -> TracePlan {
    let _ = trace;
    assert!(width <= WINDOW);
    let mut ahead = Ahead::new(steps);
    let trivial = steps.iter().all(|s| matches!(s, Step::Start(_) | Step::Back(_) | Step::Exit { .. }));
    let mut plan = TracePlan {
        windows: vec![[None; WINDOW]; steps.len()],
        skips: vec![0; steps.len()],
        unboxed: vec![0; steps.len()],
        dirty: vec![Slots::default(); steps.len()],
        exits: vec![None; steps.len()],
        trivial,
    };
    let mut alloc = WindowAlloc { width, cache: hint.clone() };
    for (step, s) in steps.iter().enumerate() {
        match s {
            Step::Start(rise) => {
                let now = alloc.cache();
                let worth = |slot: usize| ahead.worth(slot, step, now.dirty.contains(&slot));
                let mut regs = [None; WINDOW];
                let mut dirty = Slots::default();
                match rise {
                    _ if trivial => {
                        for (reg, slot) in now.slots() {
                            regs[reg] = Some(slot);
                            if now.dirty.contains(&slot) {
                                dirty.insert(slot);
                            }
                        }
                    }
                    Some(Rise { reads, writes }) => {
                        // The values worth most, those the trace brings in
                        // place. One it doesn't bring is loaded only for an
                        // event that pays, not to be live along a side exit.
                        let brought = now.slots().map(|(_, slot)| slot).filter(|&slot| reads.contains(slot));
                        let fresh = reads.iter().filter(|&slot| now.position(slot).is_none() && ahead.pays(slot, step, false).is_some());
                        let mut values: SmallVec<[((bool, usize), usize); 16]> = brought.chain(fresh).filter_map(|slot| Some((worth(slot)?, slot))).collect();
                        values.sort_unstable();
                        values.truncate(width);
                        for &(_, slot) in &values {
                            if let Some(reg) = now.position(slot) {
                                regs[reg] = Some(slot);
                            }
                        }
                        for &(_, slot) in &values {
                            if now.position(slot).is_none() {
                                let reg = (0..width).find(|&reg| regs[reg].is_none()).expect("a free register");
                                regs[reg] = Some(slot);
                            }
                        }
                        regs.iter().flatten().filter(|&&slot| writes.contains(slot)).for_each(|&slot| dirty.insert(slot));
                    }
                    None => {
                        for (reg, slot) in now.slots() {
                            if worth(slot).is_some() {
                                regs[reg] = Some(slot);
                                if now.dirty.contains(&slot) {
                                    dirty.insert(slot);
                                }
                            }
                        }
                    }
                }
                // Each value in the form its next read wants, else the one it
                // has; a trivial trace's as the hint has it. See Note [Unboxed
                // doubles].
                let mut unboxed = 0;
                for (reg, &slot) in regs.iter().enumerate() {
                    let Some(slot) = slot else { continue };
                    let has = now.source(slot, false).is_some_and(|src| src.unboxed);
                    let form = if trivial { bit(now.unboxed, reg) } else { ahead.next_form(slot, step).unwrap_or(has) };
                    unboxed |= u8::from(form) << reg;
                }
                let entry = Cache { regs, unboxed, dirty: dirty.iter().collect() };
                #[cfg(feature = "tracing")]
                crate::tracing::instant("alloc", "start", &[
                    ("trace", trace.into()),
                    ("step", step.into()),
                    ("rise", usize::from(rise.is_some()).into()),
                    ("arrives", format!("{now}").as_str().into()),
                    ("worth", worths(&ahead, now, step).as_str().into()),
                    ("entry", format!("{entry}").as_str().into()),
                ]);
                alloc = WindowAlloc { width, cache: entry };
                ahead.entered(step, &regs, unboxed);
                plan.windows[step] = regs;
                plan.unboxed[step] = unboxed;
                plan.dirty[step] = dirty;
            }
            Step::Op(op, usable) => {
                let (want, skip) = place(&alloc, &ahead, step, *op, usable);
                #[cfg(feature = "tracing")]
                let (before, worth) = (format!("{}", alloc.cache()), worths(&ahead, alloc.cache(), step));
                let mut emits = alloc.reconcile(&want, *op, skip);
                emits.extend(alloc.op(*op, [skip]).expect("a placed op runs at its SKIP"));
                #[cfg(feature = "tracing")]
                crate::tracing::instant("alloc", "op", &[
                    ("trace", trace.into()),
                    ("step", step.into()),
                    ("name", op.name().into()),
                    ("before", before.as_str().into()),
                    ("worth", worth.as_str().into()),
                    ("skip", skip.into()),
                    ("emits", emits.iter().map(|emit| emit.to_string()).collect::<Vec<_>>().join("; ").as_str().into()),
                    ("after", format!("{}", alloc.cache()).as_str().into()),
                ]);
                let _ = emits;
                plan.windows[step] = want;
                plan.skips[step] = skip;
            }
            Step::Flush => {
                #[cfg(feature = "tracing")]
                crate::tracing::instant("alloc", "flush", &[("trace", trace.into()), ("step", step.into()), ("window", format!("{}", alloc.cache()).as_str().into())]);
                alloc.flush();
            }
            Step::Exit { hot, .. } => {
                #[cfg(feature = "tracing")]
                crate::tracing::instant("alloc", "exit", &[
                    ("trace", trace.into()),
                    ("step", step.into()),
                    ("hot", usize::from(*hot).into()),
                    ("window", format!("{}", alloc.cache()).as_str().into()),
                ]);
                let _ = hot;
                plan.exits[step] = Some(alloc.cache().clone());
            }
            Step::Read(_) | Step::Back(_) => {}
        }
    }
    plan
}

/// Where the op at `step` runs, and the window it wants: its inputs in its
/// run, and the values worth most of the others, as many as fit outside it.
/// See Note [Trace allocation].
fn place(alloc: &WindowAlloc, ahead: &Ahead, step: usize, op: &dyn Window, usable: &[usize]) -> (Placement, usize) {
    let (slots, accesses) = (op.operands(), op.accesses());
    let now = alloc.cache();
    let width = alloc.width;
    let mut kept: SmallVec<[((bool, usize), usize); WINDOW]> = now
        .slots()
        .filter(|(_, slot)| !slots.contains(slot))
        .filter_map(|(_, slot)| Some((ahead.worth(slot, step, now.dirty.contains(&slot))?, slot)))
        .collect();
    kept.sort_unstable();
    kept.truncate(width - slots.len());
    // A kept value stays in a register outside the run caching it, if any.
    let outside = |slot: usize, run: &std::ops::Range<usize>| (0..width).find(|reg| !run.contains(reg) && now.regs[*reg] == Some(slot));
    let inputs = |skip: usize| (skip..).zip(slots.iter().zip(accesses)).filter(|(_, (_, a))| a.reads()).map(|(reg, (&slot, _))| (reg, slot));
    let moves = |skip: usize| {
        let run = skip..skip + slots.len();
        let misplaced = inputs(skip).filter(|&(reg, slot)| now.regs[reg] != Some(slot) && now.position(slot).is_some()).count();
        misplaced + kept.iter().filter(|&&(_, slot)| outside(slot, &run).is_none()).count()
    };
    let skip = usable.iter().copied().filter(|&skip| skip + slots.len() <= width).min_by_key(|&skip| (moves(skip), skip)).expect("a usable SKIP");
    let run = skip..skip + slots.len();
    let mut want = [None; WINDOW];
    for (reg, slot) in inputs(skip) {
        want[reg] = Some(slot);
    }
    for &(_, slot) in &kept {
        if let Some(reg) = outside(slot, &run) {
            want[reg] = Some(slot);
        }
    }
    // A kept value only in the run moves out, to an empty register if there
    // is one, else over a clean value, else over a dirty one, which is stored.
    for &(_, slot) in kept.iter().filter(|&&(_, slot)| outside(slot, &run).is_none()) {
        let reg = (0..width)
            .filter(|&reg| !run.contains(&reg) && want[reg].is_none())
            .min_by_key(|&reg| (now.regs[reg].map(|s| 1 + usize::from(now.dirty.contains(&s))), reg))
            .expect("room outside the run");
        want[reg] = Some(slot);
    }
    (want, skip)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Source {
    Reg(Loc),
    Memory(usize),
}

/// Add filling `dst` with `slot`'s value, from `src` if a register has it, to
/// `moves`; else from its stack home, or, if another destination already loads
/// it, to `copies`, to copy from that one after the parallel move.
fn fill(moves: &mut SmallVec<[(Loc, Source); 8]>, copies: &mut SmallVec<[(Loc, Loc); WINDOW]>, dst: Loc, slot: usize, src: Option<Loc>) {
    match src {
        Some(src) => moves.push((dst, Source::Reg(src))),
        None => match moves.iter().find(|(_, src)| *src == Source::Memory(slot)) {
            Some(&(first, _)) => copies.push((dst, first)),
            None => moves.push((dst, Source::Memory(slot))),
        },
    }
}

/// Emit the parallel move `moves` (distinct destinations) as a sequence of
/// moves and loads. A register's halves are distinct locations, and an axle
/// is broken through the scratch of its destination's half. See Note
/// [Parallel moves].
fn parallel_move(moves: &mut SmallVec<[(Loc, Source); 8]>, emits: &mut SmallVec<[Emit; 16]>) {
    moves.retain(|(dst, src)| *src != Source::Reg(*dst));
    while !moves.is_empty() {
        let read = |loc: Loc, moves: &[(Loc, Source)]| moves.iter().any(|(_, src)| *src == Source::Reg(loc));
        match moves.iter().position(|&(dst, _)| !read(dst, moves)) {
            Some(i) => {
                let (dst, src) = moves.remove(i);
                emits.push(match src {
                    Source::Reg(src) => Emit::Move { dst, src },
                    Source::Memory(slot) => Emit::Load { reg: dst.reg, slot, unboxed: dst.unboxed },
                });
            }
            None => {
                // Every destination is still read: an axle. Save one in SCRATCH.
                let (dst, _) = moves[0];
                let scratch = Loc { reg: SCRATCH, unboxed: dst.unboxed };
                emits.push(Emit::Move { dst: scratch, src: dst });
                for (_, src) in moves.iter_mut() {
                    if *src == Source::Reg(dst) {
                        *src = Source::Reg(scratch);
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
        *d = LBoxed::from_number(crate::unchecked_unwrap(a.as_number()) + crate::unchecked_unwrap(b.as_number()));
    });
    windowed!(BinFirst, [], [], |owner, state, base| (out d, a, b) {
        *d = LBoxed::from_number(crate::unchecked_unwrap(a.as_number()) + crate::unchecked_unwrap(b.as_number()));
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
    windowed!(Loop, [], [], |owner, state, base| (i, l, s, out v) {
        *v = i;
        core::hint::black_box((l, s));
    });

    /// A test op that takes and gives the operands of `1` unboxed.
    #[derive(Debug)]
    struct Doubles(Box<dyn Window>, u8);

    impl Window for Doubles {
        fn name(&self) -> &'static str { self.0.name() }
        fn operands(&self) -> &[usize] { self.0.operands() }
        fn accesses(&self) -> &'static [Access] { self.0.accesses() }
        fn captures(&self) -> crate::window::Captures { self.0.captures() }
        fn arity(&self) -> usize { self.0.arity() }
        fn stencil(&self, skip: usize) -> usize { self.0.stencil(skip) }
        fn next(&self) -> usize { self.0.next() }
        fn doubles(&self) -> u8 { self.1 }
        unsafe fn run<'src, 'intern>(&self, owner: &mut crate::Owner, state: &mut crate::vm::RunState<'src, 'intern>, base: *mut LBoxed<'src, 'intern>, w: &mut crate::window::Regs<'src, 'intern>, skip: usize) {
            unsafe { self.0.run(owner, state, base, w, skip) }
        }
        fn on_stack<'src, 'intern>(&self, owner: &mut crate::Owner, state: &mut crate::vm::RunState<'src, 'intern>) { self.0.on_stack(owner, state) }
    }

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
        /// A for loop step, `(idx, limit, step, out var)`.
        Loop(usize, usize, usize, usize),
    }

    /// Executes allocator output on symbolic values (slot, version), each
    /// register's halves apart, checking that every op reads the current
    /// version of its inputs in the forms it takes them, every store writes a
    /// current version, and after the run the stack holds every slot's latest
    /// version.
    #[derive(Debug, Default, Clone)]
    struct Machine {
        memory: HashMap<usize, u32>,
        current: HashMap<usize, u32>,
        regs: [Option<(usize, u32)>; WINDOW + 1],
        xregs: [Option<(usize, u32)>; WINDOW + 1],
    }

    impl Machine {
        fn version(map: &HashMap<usize, u32>, slot: usize) -> u32 {
            map.get(&slot).copied().unwrap_or(0)
        }
        fn half(&mut self, loc: Loc) -> &mut Option<(usize, u32)> {
            if loc.unboxed { &mut self.xregs[loc.reg] } else { &mut self.regs[loc.reg] }
        }
        /// The window `cache` holds, its slots at their current versions.
        fn holding(&mut self, cache: &Cache) {
            for (reg, slot) in cache.regs.iter().enumerate() {
                let value = slot.map(|slot| (slot, Self::version(&self.current, slot)));
                *self.half(cache.loc(reg)) = value;
            }
        }
        /// Whether every register of `cache` holds its slot's current value in
        /// its form.
        fn check(&mut self, cache: &Cache, what: &str) {
            for (reg, slot) in cache.regs.iter().enumerate() {
                if let Some(slot) = *slot {
                    let current = Self::version(&self.current, slot);
                    assert_eq!(*self.half(cache.loc(reg)), Some((slot, current)), "{what}: register {reg} of {cache}");
                }
            }
        }
        fn exec(&mut self, emit: Emit, op: Option<&dyn Window>) {
            match emit {
                Emit::Load { reg, slot, unboxed } => {
                    *self.half(Loc { reg, unboxed }) = Some((slot, Self::version(&self.memory, slot)));
                }
                Emit::Store { slot, reg, unboxed } => {
                    let current = Self::version(&self.current, slot);
                    assert_eq!(*self.half(Loc { reg, unboxed }), Some((slot, current)), "store of a stale value");
                    self.memory.insert(slot, current);
                }
                Emit::Move { dst, src } => {
                    *self.half(dst) = *self.half(src);
                }
                Emit::Op { skip } => {
                    let op = op.expect("an op");
                    let operands = op.operands().iter().zip(op.accesses()).enumerate();
                    for (i, (&slot, _)) in operands.clone().filter(|(_, (_, a))| a.reads()) {
                        let current = Self::version(&self.current, slot);
                        let loc = Loc { reg: skip + i, unboxed: bit(op.doubles(), i) };
                        assert_eq!(*self.half(loc), Some((slot, current)), "input {i} of {op:?}");
                    }
                    for (i, (&slot, _)) in operands.filter(|(_, (_, a))| a.writes()) {
                        let version = Self::version(&self.current, slot) + 1;
                        self.current.insert(slot, version);
                        *self.half(Loc { reg: skip + i, unboxed: bit(op.doubles(), i) }) = Some((slot, version));
                    }
                }
            }
        }
    }

    /// The ops of a run, the `i`th taking the operands of `doubles(i)` unboxed.
    fn windows(ops: &[TestOp], doubles: impl Fn(usize) -> u8) -> Vec<Box<dyn Window>> {
        ops.iter()
            .enumerate()
            .map(|(i, op)| -> Box<dyn Window> {
                let w: Box<dyn Window> = match *op {
                    TestOp::Bin(a, b, d) => Box::new(Bin::new(&[a, b, d])),
                    TestOp::BinFirst(a, b, d) => Box::new(BinFirst::new(&[d, a, b])),
                    TestOp::Get(a, d) => Box::new(Get::new(&[a, d])),
                    TestOp::Set(a, b) => Box::new(Set::new(&[a, b])),
                    TestOp::Store(a, b, c) => Box::new(Store::new(&[a, b, c])),
                    TestOp::Out(d) => Box::new(Out::new(&[d])),
                    TestOp::Loop(i, l, s, v) => Box::new(Loop::new(&[i, l, s, v])),
                };
                match doubles(i) & ((1 << w.arity()) - 1) {
                    0 => w,
                    mask => Box::new(Doubles(w, mask)),
                }
            })
            .collect()
    }

    /// Allocate a run streaming and execute it in a window of `width` registers.
    fn run(width: usize, ops: &[TestOp], doubles: impl Fn(usize) -> u8) {
        let windows = windows(ops, doubles);
        let mut alloc = WindowAlloc::with_width(width);
        let mut machine = Machine::default();
        for w in &windows {
            for emit in alloc.op(&**w, 0..WINDOW).unwrap() {
                machine.exec(emit, Some(&**w));
            }
        }
        finish(alloc, machine, ops)
    }

    /// Plan a run as a trace of one block, then execute it as planned in a
    /// window of `width` registers.
    fn run_planned(width: usize, ops: &[TestOp], doubles: impl Fn(usize) -> u8) {
        let windows = windows(ops, doubles);
        let steps: Vec<Step> =
            std::iter::once(Step::Start(None)).chain(windows.iter().map(|w| Step::Op(&**w, (0..WINDOW).collect()))).collect();
        let plan = plan_trace(&steps, width, &Cache::default(), 0);
        let mut alloc = WindowAlloc::with_width(width);
        let mut machine = Machine::default();
        for (i, w) in windows.iter().enumerate() {
            for emit in alloc.reconcile(&plan.windows[i + 1], &**w, plan.skips[i + 1]) {
                machine.exec(emit, None);
            }
            for emit in alloc.op(&**w, [plan.skips[i + 1]]).unwrap() {
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
    /// and planned, with every operand boxed, and with ops taking some unboxed.
    #[test]
    fn exhaustive_small_runs() {
        let arity = |op: &TestOp| match op {
            TestOp::Bin(..) | TestOp::BinFirst(..) | TestOp::Store(..) => 3,
            TestOp::Get(..) | TestOp::Set(..) => 2,
            TestOp::Out(..) => 1,
            TestOp::Loop(..) => 4,
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
                for doubles in [|_| 0, |i| if i % 2 == 0 { 0b101 } else { 0b110 }] {
                    run(width, &ops, doubles);
                    run_planned(width, &ops, doubles);
                }
            }
        }
    }

    /// A xorshift generator, for reproducible random traces.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: usize) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % n as u64) as usize
        }
    }

    /// Random traces of ops over up to six slots, with block starts (some
    /// entered by a rising edge), jumps back to them, flushes, inline guards
    /// and exits, some ops taking some operands unboxed, in windows of 5 to 8
    /// registers, run as the JIT runs a planned
    /// trace: each op reconciled to its planned window, each block entered
    /// through a transfer into its entry window, each jump back's transfer
    /// into its target's checked, and each exit's stores. The trace starts
    /// from a window with dirty slots, and each exit is also followed through
    /// a trivial trace, to its thunk's exit and to a block the thunk is linked
    /// into. Every op reads current values, no write is lost, and the stack
    /// ends current.
    #[test]
    fn random_traces() {
        let mut rng = Rng(0x2545f4914f6cdd1d);
        for _ in 0..3000 {
            let width = 5 + rng.below(WINDOW - 4);
            let mut ops = Vec::new();
            let mut kinds = Vec::new();
            let mut starts = vec![0];
            for _ in 0..1 + rng.below(24) {
                let step = kinds.len() + 1;
                let k = rng.below(14);
                let mut slot = || rng.below(6);
                match k {
                    0 | 4 => {
                        starts.push(step);
                        kinds.push((if k == 0 { 1 } else { 5 }, 0));
                    }
                    1 => kinds.push((2, 0)),
                    2 => kinds.push((3, 0)),
                    3 => kinds.push((4, slot())),
                    5 => kinds.push((6, starts[slot() % starts.len()])),
                    k => {
                        ops.push(match k {
                            6..=8 => B(slot(), slot(), slot()),
                            9 => TestOp::BinFirst(slot(), slot(), slot()),
                            10 => G(slot(), slot()),
                            11 => S(slot(), slot()),
                            12 => U(slot()),
                            _ => L(slot(), slot(), slot(), slot()),
                        });
                        kinds.push((0, 0));
                    }
                }
            }
            let masks: Vec<u8> = ops.iter().map(|_| rng.below(16) as u8 * u8::from(rng.below(2) == 0)).collect();
            let windows = windows(&ops, |i| masks[i]);
            let mut next_op = windows.iter();
            let some_slots = |rng: &mut Rng| {
                let mut slots = Slots::default();
                (0..rng.below(4)).for_each(|_| slots.insert(rng.below(6)));
                slots
            };
            let steps: Vec<Step> = std::iter::once(Step::Start(None))
                .chain(kinds.iter().map(|&(kind, arg)| match kind {
                    0 => Step::Op(&**next_op.next().unwrap(), (0..WINDOW).collect()),
                    1 => Step::Start(None),
                    2 => Step::Flush,
                    3 => Step::Exit { hot: rng.below(2) == 0, reads: some_slots(&mut rng) },
                    4 => Step::Read(arg),
                    5 => Step::Start(Some(Rise { reads: some_slots(&mut rng), writes: some_slots(&mut rng) })),
                    _ => Step::Back(arg),
                }))
                .collect();
            // Any window over `width` registers, some of its slots dirty.
            let some_window = |rng: &mut Rng| {
                let mut window = Cache::default();
                for reg in 0..rng.below(width + 1) {
                    let slot = rng.below(6);
                    if window.position(slot).is_none() {
                        window.set(reg, Some(slot), rng.below(2) == 0);
                        if rng.below(2) == 0 {
                            window.dirty.push(slot);
                        }
                    }
                }
                window
            };
            let hint = some_window(&mut rng);
            let plan = plan_trace(&steps, width, &hint, 0);
            let mut machine = Machine::default();
            for &slot in &hint.dirty {
                machine.current.insert(slot, 1);
            }
            machine.holding(&hint);
            let mut alloc = WindowAlloc { width, cache: hint };
            let mut entries = HashMap::new();
            for (step, s) in steps.iter().enumerate() {
                match s {
                    Step::Start(rise) => {
                        let from = if rise.is_some() { Cache::default() } else { alloc.cache().clone() };
                        let entry = Cache::entry(plan.windows[step], plan.unboxed[step], &from, &plan.dirty[step]);
                        for emit in alloc.transfer(&entry) {
                            machine.exec(emit, None);
                        }
                        entries.insert(step, entry.clone());
                        alloc = WindowAlloc { width, cache: entry };
                    }
                    Step::Op(op, _) => {
                        for emit in alloc.reconcile(&plan.windows[step], *op, plan.skips[step]) {
                            machine.exec(emit, None);
                        }
                        for emit in alloc.op(*op, [plan.skips[step]]).unwrap() {
                            machine.exec(emit, Some(*op));
                        }
                    }
                    Step::Flush => {
                        for emit in alloc.flush() {
                            machine.exec(emit, None);
                        }
                    }
                    Step::Back(start) => {
                        let entry = &entries[start];
                        let mut taken = machine.clone();
                        for emit in alloc.transfer(entry) {
                            taken.exec(emit, None);
                        }
                        taken.check(entry, &format!("back edge at step {step} of {ops:?}"));
                        for (&slot, &version) in taken.current.iter().filter(|(slot, _)| !entry.dirty.contains(slot)) {
                            assert_eq!(Machine::version(&taken.memory, slot), version, "slot {slot} stale at the back edge at step {step} of {ops:?}");
                        }
                    }
                    Step::Exit { .. } => {
                        let mut taken = machine.clone();
                        for emit in alloc.stores() {
                            taken.exec(emit, None);
                        }
                        for (&slot, &version) in &taken.current {
                            assert_eq!(Machine::version(&taken.memory, slot), version, "slot {slot} stale at the exit at step {step} of {ops:?}");
                        }
                        // The exit into a thunk-only block, a trivial trace
                        // planned from the window the plan leaves here: its
                        // thunk's exit, and the thunk linked into a block
                        // entered with any window, lose no write.
                        let trivial = plan_trace(&[Step::Start(None)], width, plan.exits[step].as_ref().unwrap(), 0);
                        let entry = Cache::entry(trivial.windows[0], trivial.unboxed[0], alloc.cache(), &trivial.dirty[0]);
                        let mut linked = machine.clone();
                        for emit in alloc.transfer(&entry) {
                            linked.exec(emit, None);
                        }
                        let thunk = WindowAlloc { width, cache: entry };
                        let mut exited = linked.clone();
                        for emit in thunk.stores() {
                            exited.exec(emit, None);
                        }
                        for (&slot, &version) in &exited.current {
                            assert_eq!(Machine::version(&exited.memory, slot), version, "slot {slot} stale at the thunk after step {step} of {ops:?}");
                        }
                        let target = some_window(&mut rng);
                        for emit in thunk.transfer(&target) {
                            linked.exec(emit, None);
                        }
                        linked.check(&target, &format!("link after step {step} of {ops:?}"));
                        for (&slot, &version) in linked.current.iter().filter(|(slot, _)| !target.dirty.contains(slot)) {
                            assert_eq!(Machine::version(&linked.memory, slot), version, "slot {slot} lost by the link after step {step} of {ops:?} into {target:?}");
                        }
                    }
                    Step::Read(_) => {}
                }
            }
            finish(alloc, machine, &ops);
        }
    }

    /// Every window over three registers and three slots (each register caching
    /// a slot or nothing, each cached slot dirty or not, every value boxed, or
    /// unboxed, or only the second register's) transfers to every other:
    /// afterwards the target's registers hold their slots' current values in
    /// their forms, and every slot it doesn't carry dirty is current on the
    /// stack. A window transfers to itself with no code.
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
                let dirty: SmallVec<[usize; WINDOW]> = cached.iter().enumerate().filter(|(i, _)| mask & 1 << i != 0).map(|(_, &slot)| slot).collect();
                for unboxed in [0, 0b111, 0b010] {
                    caches.push(Cache { regs, unboxed: unboxed & occupied(&regs), dirty: dirty.clone() });
                }
            }
        }
        for from in &caches {
            for to in &caches {
                let mut machine = Machine::default();
                for &slot in &from.dirty {
                    machine.current.insert(slot, 1);
                }
                machine.holding(from);
                let emits = WindowAlloc::entering(from.clone()).transfer(to);
                assert!(from != to || emits.is_empty(), "{from:?} to itself: {emits:?}");
                for emit in emits {
                    machine.exec(emit, None);
                }
                machine.check(to, &format!("{from} to {to}"));
                for slot in (0..SLOTS).filter(|slot| !to.dirty.contains(slot)) {
                    let current = Machine::version(&machine.current, slot);
                    assert_eq!(Machine::version(&machine.memory, slot), current, "{from:?} to {to:?}: slot {slot}");
                }
            }
        }
    }

    /// A trivial trace, a block of only a thunk or only a jump, is entered with
    /// the hint as it is and leaves it along its exit, whether or not the edge
    /// into it enters more frequent code.
    #[test]
    fn trivial_trace_forwards_its_hint() {
        let mut hint = Cache::default();
        hint.set(1, Some(4), true);
        hint.set(3, Some(2), false);
        hint.dirty.push(2);
        let rise = || Some(Rise { reads: Slots::default(), writes: Slots::default() });
        for steps in [vec![Step::Start(None)], vec![Step::Start(rise())], vec![Step::Start(None), Step::Exit { hot: true, reads: Slots::default() }]] {
            let plan = plan_trace(&steps, WINDOW, &hint, 0);
            assert!(plan.trivial);
            assert_eq!(plan.windows[0], hint.regs);
            assert_eq!(plan.unboxed[0], hint.unboxed);
            assert_eq!(plan.dirty[0].iter().collect::<Vec<_>>(), vec![2]);
            if steps.len() > 1 {
                assert_eq!(plan.exits[1].as_ref(), Some(&hint));
            }
        }
    }

    /// Cycles are broken through the scratch of a half: between general
    /// registers, between XMM registers, and between the halves of two
    /// registers, unboxing one into the other while boxing it back.
    #[test]
    fn parallel_move_cycle() {
        let w = |reg| Loc { reg, unboxed: false };
        let x = |reg| Loc { reg, unboxed: true };
        let cases: [&[(Loc, Source)]; 3] = [
            &[(w(0), Source::Reg(w(1))), (w(1), Source::Reg(w(0))), (w(2), Source::Memory(7))],
            &[(x(0), Source::Reg(x(1))), (x(1), Source::Reg(x(0)))],
            &[(x(0), Source::Reg(w(1))), (w(1), Source::Reg(x(0)))],
        ];
        for case in cases {
            let mut moves: SmallVec<[(Loc, Source); 8]> = SmallVec::from_slice(case);
            let mut emits = SmallVec::new();
            parallel_move(&mut moves, &mut emits);
            assert_eq!(emits.iter().filter(|e| matches!(e, Emit::Move { dst: Loc { reg: SCRATCH, .. }, .. })).count(), 1, "{case:?}");
            let mut machine = Machine::default();
            for reg in 0..WINDOW {
                machine.regs[reg] = Some((reg, 0));
                machine.xregs[reg] = Some((reg, 1));
            }
            let before = machine.clone();
            for emit in emits {
                machine.exec(emit, None);
            }
            for &(dst, src) in case {
                let want = match src {
                    Source::Reg(src) => *before.clone().half(src),
                    Source::Memory(slot) => Some((slot, 0)),
                };
                assert_eq!(*machine.half(dst), want, "{case:?}");
            }
        }
    }
}
