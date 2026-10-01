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
    /// the window of the first jump to the block, or planned dirty in `dirty`.
    /// A clean value marked dirty is only stored again, so any slot can be.
    pub fn entry(regs: Placement, from: &Cache, dirty: &Slots) -> Cache {
        let mut dirty: SmallVec<[usize; WINDOW]> = regs.iter().flatten().copied().filter(|slot| from.dirty.contains(slot) || dirty.contains(*slot)).collect();
        dirty.sort_unstable();
        dirty.dedup();
        Cache { regs, dirty }
    }

    /// The slot each register caches.
    pub fn regs(&self) -> &Placement {
        &self.regs
    }

    fn position(&self, slot: usize) -> Option<usize> {
        self.regs.iter().position(|&s| s == Some(slot))
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

    /// Make the window hold `want` in each register it names, before `op`,
    /// leaving the others as they are: store the dirty values overwritten that
    /// survive nowhere else and that `op` doesn't rewrite, then fill the named
    /// registers as one parallel move (a slot loaded into several registers is
    /// loaded once and copied). See Note [Window allocation].
    pub fn reconcile(&mut self, want: &Placement, op: &dyn Window) -> SmallVec<[Emit; 16]> {
        let rewritten = |slot: usize| op.operands().iter().zip(op.accesses()).any(|(&s, &a)| s == slot && a.writes());
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
            match (0..i).find(|&j| accesses[j].reads() && slots[j] == slot) {
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
            if access.writes() {
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
    /// Per block start, the slots its entry window has dirty.
    pub dirty: Vec<Slots>,
    /// Per `Exit`, the window the trace leaves along it.
    pub exits: Vec<Option<Cache>>,
}

/// What lies ahead of each step of a trace, for the worth of keeping a value.
/// See Note [Trace allocation].
struct Ahead {
    /// Per slot, the steps reading (`true`) or writing it, in order.
    events: Vec<Vec<(usize, bool)>>,
    /// Per slot, the side exits it is live along, in order.
    leaves: Vec<Vec<usize>>,
    flushes: Vec<usize>,
    /// Each jump back into the trace, `(back, start)`.
    backs: Vec<(usize, usize)>,
}

impl Ahead {
    fn new(steps: &[Step]) -> Ahead {
        let mut ahead = Ahead { events: vec![Vec::new(); 256], leaves: vec![Vec::new(); 256], flushes: Vec::new(), backs: Vec::new() };
        for (step, s) in steps.iter().enumerate() {
            match s {
                Step::Op(op, _) => {
                    for (&slot, &access) in op.operands().iter().zip(op.accesses()) {
                        if access.reads() {
                            ahead.events[slot].push((step, true));
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

    /// The block starting at step `start` is entered with `window`: each jump
    /// back to it reads that.
    fn entered(&mut self, start: usize, window: &Placement) {
        for &(back, _) in self.backs.iter().filter(|&&(_, s)| s == start) {
            for &slot in window.iter().flatten() {
                let events = &mut self.events[slot];
                events.insert(events.partition_point(|e| e.0 < back), (back, true));
            }
        }
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

/// Plan a trace's window ops in a window of `width` registers, its head
/// entered from `hint`. See Note [Trace allocation].
pub fn plan_trace(steps: &[Step], width: usize, hint: &Cache) -> TracePlan {
    assert!(width <= WINDOW);
    let mut ahead = Ahead::new(steps);
    let mut plan = TracePlan {
        windows: vec![[None; WINDOW]; steps.len()],
        skips: vec![0; steps.len()],
        dirty: vec![Slots::default(); steps.len()],
        exits: vec![None; steps.len()],
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
                let entry = Cache { regs, dirty: dirty.iter().collect() };
                alloc = WindowAlloc { width, cache: entry };
                ahead.entered(step, &regs);
                plan.windows[step] = regs;
                plan.dirty[step] = dirty;
            }
            Step::Op(op, usable) => {
                let (want, skip) = place(&alloc, &ahead, step, *op, usable);
                alloc.reconcile(&want, *op);
                alloc.op(*op, [skip]).expect("a placed op runs at its SKIP");
                plan.windows[step] = want;
                plan.skips[step] = skip;
            }
            Step::Flush => {
                alloc.flush();
            }
            Step::Exit { .. } => plan.exits[step] = Some(alloc.cache().clone()),
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
                    for (i, (&slot, _)) in operands.clone().filter(|(_, (_, a))| a.reads()) {
                        let current = Self::version(&self.current, slot);
                        assert_eq!(self.regs[skip + i], Some((slot, current)), "input {i} of {op:?}");
                    }
                    for (i, (&slot, _)) in operands.filter(|(_, (_, a))| a.writes()) {
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
                    TestOp::Loop(i, l, s, v) => Box::new(Loop::new(&[i, l, s, v])),
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

    /// Plan a run as a trace of one block, then execute it as planned in a
    /// window of `width` registers.
    fn run_planned(width: usize, ops: &[TestOp]) {
        let windows = windows(ops);
        let steps: Vec<Step> =
            std::iter::once(Step::Start(None)).chain(windows.iter().map(|w| Step::Op(&**w, (0..WINDOW).collect()))).collect();
        let plan = plan_trace(&steps, width, &Cache::default());
        let mut alloc = WindowAlloc::with_width(width);
        let mut machine = Machine::default();
        for (i, w) in windows.iter().enumerate() {
            for emit in alloc.reconcile(&plan.windows[i + 1], &**w) {
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
    /// and planned.
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
                run(width, &ops);
                run_planned(width, &ops);
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
    /// and exits, in windows of 5 to 8 registers, run as the JIT runs a planned
    /// trace: each op reconciled to its planned window, each block entered
    /// through a transfer into its entry window, each jump back's transfer
    /// into its target's checked, and each exit's stores. Every op reads
    /// current values and the stack ends current.
    #[test]
    fn random_traces() {
        let mut rng = Rng(0x2545f4914f6cdd1d);
        for _ in 0..3000 {
            let width = 5 + rng.below(5);
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
            let windows = windows(&ops);
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
            let mut hint = Cache::default();
            for reg in 0..rng.below(width) {
                let slot = rng.below(6);
                if hint.position(slot).is_none() {
                    hint.regs[reg] = Some(slot);
                }
            }
            let plan = plan_trace(&steps, width, &hint);
            let mut machine = Machine::default();
            for (reg, slot) in hint.regs.iter().enumerate() {
                machine.regs[reg] = slot.map(|slot| (slot, 0));
            }
            let mut alloc = WindowAlloc { width, cache: hint };
            let mut entries = HashMap::new();
            for (step, s) in steps.iter().enumerate() {
                match s {
                    Step::Start(rise) => {
                        let from = if rise.is_some() { Cache::default() } else { alloc.cache().clone() };
                        let entry = Cache::entry(plan.windows[step], &from, &plan.dirty[step]);
                        for emit in alloc.transfer(&entry) {
                            machine.exec(emit, None);
                        }
                        entries.insert(step, entry.clone());
                        alloc = WindowAlloc { width, cache: entry };
                    }
                    Step::Op(op, _) => {
                        for emit in alloc.reconcile(&plan.windows[step], *op) {
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
                        let mut taken = Machine { memory: machine.memory.clone(), current: machine.current.clone(), regs: machine.regs };
                        for emit in alloc.transfer(entry) {
                            taken.exec(emit, None);
                        }
                        for (reg, slot) in entry.regs.iter().enumerate() {
                            if let Some(slot) = *slot {
                                let current = Machine::version(&taken.current, slot);
                                assert_eq!(taken.regs[reg], Some((slot, current)), "back edge at step {step} of {ops:?}");
                            }
                        }
                        for (&slot, &version) in taken.current.iter().filter(|(slot, _)| !entry.dirty.contains(slot)) {
                            assert_eq!(Machine::version(&taken.memory, slot), version, "slot {slot} stale at the back edge at step {step} of {ops:?}");
                        }
                    }
                    Step::Exit { .. } => {
                        let mut taken = Machine { memory: machine.memory.clone(), current: machine.current.clone(), regs: machine.regs };
                        for emit in alloc.stores() {
                            taken.exec(emit, None);
                        }
                        for (&slot, &version) in &taken.current {
                            assert_eq!(Machine::version(&taken.memory, slot), version, "slot {slot} stale at the exit at step {step} of {ops:?}");
                        }
                    }
                    Step::Read(_) => {}
                }
            }
            finish(alloc, machine, &ops);
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
