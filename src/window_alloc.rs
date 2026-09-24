//! Register allocation for window ops in the JIT: which window register caches
//! which stack slot. Placements are decided bottom-up over a compiled region,
//! then code is generated top-down. See Note [Register window] and Note [Window
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
// * Backward, deciding placements, one trace at a time ([`plan_trace`], Note
//   [Trace allocation]). A `Placement` says which slot's current value the
//   code wants in each register before a window op, and at a block's start
//   (its entry window); each op gets its `SKIP`.
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
// window takes its dirty slots from the first jump to it that is compiled, and
// from its plan: a loop header's has the slots the loop writes dirty, as its
// back edge brings them, so the back edge doesn't store them every iteration.
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

// What planning a trace charges for the code a placement implies (Note [Trace
// allocation]). A move between registers is renamed away and costs only its
// bytes; a load of an L1-resident stack slot is cheap out of order; a store
// is dearest, and one reloaded soon after waits on store forwarding.
const PLAN_MOVE: u32 = 1;
const PLAN_LOAD: u32 = 2;
const PLAN_STORE: u32 = 5;

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
        let dirty = regs.iter().flatten().copied().filter(|slot| from.dirty.contains(slot) || dirty.contains(*slot)).collect();
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

// Note [Trace allocation]
// ~~~~~~~~~~~~~~~~~~~~~~~
// A trace is planned by one backward pass over its steps, destination-driven
// (docs/trace-register-allocation.md, Allocating a trace). The window is
// positional: an op reads `w[SKIP..]` and writes above its inputs, so a value
// is worth a register only where it sits in place for its next use, and a load
// into that place costs what a move does. Rather than pinning every value some
// later op wants, the pass keeps a request per pending use: in a register (the
// operand position of a placed op, or any register, moved into place at the
// use), or dropped to its stack home (loaded at the use).
//
// Walking up, each op is placed at the usable `SKIP` cheapest against the
// pending requests: a request of another slot in its run is demoted (a move or
// a load at its use, and a store if its value is dirty), never moved aside and
// back; an output or input in another register than a request of its slot
// wants is a move, and so is an input its producer in the trace can't write in
// place. A forward pre-pass finds where each op's output can be produced: the
// registers it lands in at the usable `SKIP`s where the fewest of the op's own
// inputs miss the places their producers can write them. Ties go to demoting
// the requests used furthest down, then to the lowest `SKIP`: the pre-pass has
// kept room below it for its producers, and a chain placed low leaves the
// registers above it to values kept between their uses (an accumulator, a
// value read by every repetition of an op shape). Its outputs, then its
// inputs, are the sources of their slots' pending requests: those keep their
// register from here to their use, or, wanting any register, keep the source's
// if it is free that long, else are dropped. Its inputs then request their
// places from the code above.
//
// A register is free for a value from the current step to its use if no request
// holds it and nothing occupies it before the use: every run and every kept
// value between was placed on the way up, so each register records the
// earliest step occupying it, and checking is constant time. Requests wanting
// any register are capped at the window's width, dropping the furthest used.
// Flush points drop every request; at the top of the trace, requests for a
// register are its entry window and the others are dropped. So they are at a
// loop header's start, where the code above is then asked for that window:
// requests from the loop's body end at its header, rather than reaching up to
// sources above the loop, where the code before it would drop them and the
// loop would reload them every iteration. (A trace with a loop is planned
// twice, the latch continuing into the header's window from the first pass.)
//
// Exits to blocks outside the trace are the thesis's pseudo-uses, and so is a
// thunk's exit to the interpreter, which reads the stack, of every slot dirty
// there. They are the cold edges: moving a value into place for one, or
// loading it there, costs nothing. But a dirty value that loses its register
// before the exit is stored on the way, on the hot path, and that store is
// costed, whichever exit needs the value: an op writing over the register it
// sits in otherwise evicts it for free, and codegen stores it anyway. Capping
// drops them before the trace's own requests. The windows wanted before each
// step are read off the kept intervals afterwards.

/// A step of a trace, for [`plan_trace`]: its blocks' residuals, as planning
/// sees them.
pub enum Step<'a> {
    /// A block's start: the window planned here is its entry window.
    Start,
    /// The start of a loop's header, the target of a back edge in the trace.
    /// See Note [Trace allocation].
    Header,
    /// A window op, and the `SKIP`s it can run at.
    Op(&'a dyn Window, SmallVec<[usize; WINDOW]>),
    /// A residual that flushes the window.
    Flush,
    /// An edge leaving the trace into a block entered with `window`: the
    /// trace's continuation if `own`, else a pseudo-use.
    Exit { window: Placement, own: bool },
    /// An edge leaving the trace into a block with no window yet, which these
    /// slots are live into: pseudo-uses that may stay in memory.
    ExitLive(SmallVec<[usize; 16]>),
    /// A thunk: an exit to the interpreter, which reads the stack, so the
    /// slots dirty there are pseudo-uses.
    Thunk,
}

/// A planned trace: per step, the placement wanted before it (an op's, or a
/// block's entry window at its `Start`), an op's `SKIP`, and at a loop's
/// `Header`, the slots its entry window has dirty: those the loop writes,
/// which its back edge brings dirty (see Note [Trace allocation]).
pub struct TracePlan {
    pub windows: Vec<Placement>,
    pub skips: Vec<usize>,
    pub dirty: Vec<Slots>,
    /// Every request an op demoted, for window dumps.
    pub demotions: Vec<Demotion>,
}

/// A request for `slot` in `reg`, used at step `used`, demoted by the op at
/// `step` placed at `skip` for `cost`; `kept` is the cheapest `SKIP` of that
/// op that would have kept it, and its cost, if any.
#[derive(Debug, Clone, Copy)]
pub struct Demotion {
    pub step: usize,
    pub slot: usize,
    pub reg: usize,
    pub used: usize,
    pub skip: usize,
    pub cost: u32,
    pub kept: Option<(usize, u32)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Fate {
    Pending,
    /// In `reg` from step `from` (the top of the trace if `None`) to the use.
    Kept { reg: usize, from: Option<usize> },
    /// Loaded at the use.
    Home,
}

/// A use's request for its slot. See Note [Trace allocation].
#[derive(Debug)]
struct Request {
    slot: usize,
    /// The step using it.
    at: usize,
    /// Whether the trace's own code uses it, rather than a pseudo-use.
    own: bool,
    /// The register it wants the value in, or any.
    wants: Option<usize>,
    fate: Fate,
}

struct Planner {
    width: usize,
    requests: Vec<Request>,
    /// The pending request wanting each register.
    holds: [Option<usize>; WINDOW],
    /// Pending requests wanting any register.
    any: SmallVec<[usize; WINDOW]>,
    /// The earliest step at or below the walk that occupies each register.
    occupied: [usize; WINDOW],
}

/// The op at `skip`: its operands and where they are.
struct Run<'a> {
    slots: &'a [usize],
    accesses: &'a [Access],
    skip: usize,
}

impl Run<'_> {
    fn contains(&self, reg: usize) -> bool {
        (self.skip..self.skip + self.slots.len()).contains(&reg)
    }

    /// The register the op writes `slot` to, if it writes it.
    fn writes(&self, slot: usize) -> Option<usize> {
        self.operands().find(|&(_, s, a)| s == slot && a == Access::Write).map(|(reg, ..)| reg)
    }

    /// Whether the op reads `slot` in `reg`.
    fn reads_at(&self, slot: usize, reg: usize) -> bool {
        self.contains(reg) && self.slots[reg - self.skip] == slot && self.accesses[reg - self.skip] == Access::Read
    }

    fn operands(&self) -> impl Iterator<Item = (usize, usize, Access)> + '_ {
        self.slots.iter().zip(self.accesses).enumerate().map(|(i, (&slot, &access))| (self.skip + i, slot, access))
    }
}

impl Planner {
    fn pending(&self, slot: usize) -> SmallVec<[usize; WINDOW]> {
        self.holds.iter().flatten().chain(&self.any).copied().filter(|&id| self.requests[id].slot == slot).collect()
    }

    /// Whether `reg` can keep a value until step `until`, once the op `run`
    /// is placed (its run's requests are demoted or its own).
    fn free(&self, reg: usize, until: usize, run: &Run) -> bool {
        self.occupied[reg] >= until && (self.holds[reg].is_none() || run.contains(reg))
    }

    fn keep(&mut self, id: usize, reg: usize, from: Option<usize>) {
        self.requests[id].fate = Fate::Kept { reg, from };
        if let Some(from) = from {
            self.occupied[reg] = self.occupied[reg].min(from);
        }
    }

    fn request(&mut self, slot: usize, at: usize, own: bool, wants: Option<usize>) {
        let id = self.requests.len();
        self.requests.push(Request { slot, at, own, wants, fate: Fate::Pending });
        match wants {
            Some(reg) => self.holds[reg] = Some(id),
            None => self.any.push(id),
        }
    }

    /// The cost of the op `run` against the pending requests, and the nearest
    /// use among the requests it demotes. `dirty` has the slots written in the
    /// trace since the last flush.
    fn cost(&self, run: &Run, dirty: &Slots) -> (u32, usize) {
        let weight = |id: usize| u32::from(self.requests[id].own);
        // A demoted value is reloaded at its use (a pseudo-use's, on its cold
        // edge, is free), and stored first if dirty, on the hot path.
        let dropped = |id: usize| {
            let q = &self.requests[id];
            weight(id) * PLAN_LOAD + if dirty.contains(q.slot) { PLAN_STORE } else { 0 }
        };
        let mut cost = 0;
        let mut nearest = usize::MAX;
        for reg in run.skip..run.skip + run.slots.len() {
            let Some(id) = self.holds[reg] else { continue };
            let q = &self.requests[id];
            match run.writes(q.slot) {
                Some(out) if out != reg => cost += weight(id) * PLAN_MOVE,
                Some(_) => {}
                None if run.reads_at(q.slot, reg) => {}
                None => {
                    cost += dropped(id);
                    if q.own {
                        nearest = nearest.min(q.at);
                    }
                }
            }
        }
        for (reg, slot, access) in run.operands() {
            for id in self.pending(slot) {
                let q = &self.requests[id];
                match (access, q.wants) {
                    (Access::Write, Some(r)) if !run.contains(r) => cost += weight(id) * PLAN_MOVE,
                    // Kept in its register until the use, a move there; else
                    // the new value is stored, on the hot path, and reloaded.
                    (Access::Write, None) => {
                        cost += if self.free(reg, q.at, run) { weight(id) * PLAN_MOVE } else { PLAN_STORE + weight(id) * PLAN_LOAD }
                    }
                    (Access::Read, Some(r)) if !run.contains(r) && r != reg => cost += weight(id) * PLAN_MOVE,
                    _ => {}
                }
            }
        }
        (cost, nearest)
    }

    /// Place the op `run` at step `step`.
    fn place(&mut self, step: usize, run: &Run) {
        // Requests the run overwrites are demoted.
        for reg in run.skip..run.skip + run.slots.len() {
            if let Some(id) = self.holds[reg] {
                let slot = self.requests[id].slot;
                if run.writes(slot).is_none() && !run.reads_at(slot, reg) {
                    self.holds[reg] = None;
                    self.requests[id].wants = None;
                    self.any.push(id);
                }
            }
        }
        // Outputs, then inputs, are their slots' sources. Requests for any
        // register need a free one, so go before those holding theirs.
        let outputs = run.operands().filter(|&(.., a)| a == Access::Write);
        let inputs = run.operands().filter(|&(.., a)| a == Access::Read);
        for (reg, slot, _) in outputs.chain(inputs) {
            for id in self.pending(slot) {
                if self.requests[id].wants.is_none() {
                    self.any.retain(|&mut a| a != id);
                    if self.free(reg, self.requests[id].at, run) {
                        self.keep(id, reg, Some(step));
                    } else {
                        self.requests[id].fate = Fate::Home;
                    }
                }
            }
            for id in self.pending(slot) {
                if let Some(r) = self.requests[id].wants {
                    self.holds[r] = None;
                    self.keep(id, r, Some(step));
                }
            }
        }
        for reg in run.skip..run.skip + run.slots.len() {
            self.occupied[reg] = self.occupied[reg].min(step);
        }
        for (reg, slot, access) in run.operands() {
            if access == Access::Read {
                self.request(slot, step, true, Some(reg));
            }
        }
    }

    /// Drop the requests for any register used furthest down, beyond what the
    /// window can hold.
    fn cap(&mut self) {
        while self.holds.iter().flatten().count() + self.any.len() > self.width {
            let (i, &id) = self
                .any
                .iter()
                .enumerate()
                .max_by_key(|&(_, &id)| (!self.requests[id].own, self.requests[id].at))
                .expect("a request for any register");
            self.any.remove(i);
            self.requests[id].fate = Fate::Home;
        }
    }

    /// At a loop header's start `step`: the requests for a register are its
    /// entry window, which the code above is asked for in turn, as it would
    /// be for a jump into it; the others are dropped.
    fn anchor(&mut self, step: usize) {
        for reg in 0..WINDOW {
            if let Some(id) = self.holds[reg].take() {
                self.keep(id, reg, step.checked_sub(1));
                let Request { slot, own, .. } = self.requests[id];
                self.request(slot, step, own, Some(reg));
            }
        }
        for id in self.any.drain(..) {
            self.requests[id].fate = Fate::Home;
        }
    }

    fn drop_pending(&mut self) {
        for id in self.holds.iter_mut().filter_map(Option::take).chain(self.any.drain(..)) {
            self.requests[id].fate = Fate::Home;
        }
    }
}

/// Plan a trace's window ops, walking its `steps` backward, in a window of
/// `width` registers. See Note [Trace allocation].
pub fn plan_trace(steps: &[Step], width: usize) -> TracePlan {
    assert!(width <= WINDOW);
    // The slots each step finds written in the trace since the last flush, and
    // where each op's inputs can be produced in place: the registers their
    // producer in the trace writes them to at the `SKIP`s where its own
    // inputs' producers can (or most can) write those in place in turn, as a
    // mask; any register for an input with no producer in the trace.
    let mut dirty = Vec::with_capacity(steps.len());
    let mut in_place: Vec<SmallVec<[u16; 5]>> = Vec::with_capacity(steps.len());
    let mut written = Slots::default();
    // Per slot written since the last flush, the registers its writer can put it in.
    let mut writer: SmallVec<[(usize, u16); 16]> = SmallVec::new();
    for s in steps {
        dirty.push(written);
        let mut inputs: SmallVec<[u16; 5]> = SmallVec::new();
        match s {
            Step::Op(op, usable) => {
                let operands = op.operands().iter().zip(op.accesses()).enumerate();
                for (_, (&slot, _)) in operands.clone().filter(|(_, (_, a))| **a == Access::Read) {
                    inputs.push(writer.iter().find(|w| w.0 == slot).map_or(u16::MAX, |w| w.1));
                }
                let reads = |skip: usize| (skip..).zip(op.accesses()).filter(|(_, a)| **a == Access::Read).map(|(reg, _)| reg);
                let misses = |skip: usize| reads(skip).zip(&inputs).filter(|&(reg, mask)| mask & 1 << reg == 0).count();
                let fits = usable.iter().copied().filter(|&skip| skip + op.operands().len() <= width);
                let fewest = fits.clone().map(misses).min().unwrap_or(0);
                let good = fits.filter(|&skip| misses(skip) == fewest).fold(0u16, |mask, skip| mask | 1 << skip);
                for (index, (&slot, _)) in operands.filter(|(_, (_, a))| **a == Access::Write) {
                    written.insert(slot);
                    writer.retain(|w| w.0 != slot);
                    writer.push((slot, good << index));
                }
            }
            Step::Flush => {
                written = Slots::default();
                writer.clear();
            }
            _ => {}
        }
        in_place.push(inputs);
    }
    let mut planner = Planner { width, requests: Vec::new(), holds: [None; WINDOW], any: SmallVec::new(), occupied: [usize::MAX; WINDOW] };
    let mut skips = vec![0; steps.len()];
    let mut demotions = Vec::new();
    for (step, s) in steps.iter().enumerate().rev() {
        match s {
            Step::Start => {}
            Step::Header => planner.anchor(step),
            Step::Op(op, usable) => {
                let (slots, accesses) = (op.operands(), op.accesses());
                let costed: SmallVec<[(usize, u32, usize); WINDOW]> = usable
                    .iter()
                    .copied()
                    .filter(|&skip| skip + slots.len() <= width)
                    .map(|skip| {
                        let (mut cost, nearest) = planner.cost(&Run { slots, accesses, skip }, &dirty[step]);
                        // An input its producer can't write in place is a move.
                        let inputs = (skip..).zip(accesses).filter(|(_, a)| **a == Access::Read).map(|(reg, _)| reg);
                        for (reg, mask) in inputs.zip(&in_place[step]) {
                            cost += u32::from(mask & 1 << reg == 0) * PLAN_MOVE;
                        }
                        (skip, cost, nearest)
                    })
                    .collect();
                let &(skip, cost, _) =
                    costed.iter().min_by_key(|&&(skip, cost, nearest)| (cost, std::cmp::Reverse(nearest), skip)).expect("a usable SKIP");
                let run = Run { slots, accesses, skip };
                for reg in skip..skip + slots.len() {
                    let Some(id) = planner.holds[reg] else { continue };
                    let q = &planner.requests[id];
                    if run.writes(q.slot).is_none() && !run.reads_at(q.slot, reg) {
                        let keeps = |other: usize| {
                            let run = Run { slots, accesses, skip: other };
                            !run.contains(reg) || run.writes(q.slot).is_some() || run.reads_at(q.slot, reg)
                        };
                        let kept = costed.iter().filter(|&&(other, ..)| keeps(other)).min_by_key(|&&(_, cost, _)| cost).map(|&(other, cost, _)| (other, cost));
                        demotions.push(Demotion { step, slot: q.slot, reg, used: q.at, skip, cost, kept });
                    }
                }
                planner.place(step, &run);
                skips[step] = skip;
            }
            Step::Flush => planner.drop_pending(),
            Step::Exit { window, own } => {
                for (reg, slot) in window.iter().enumerate().take(width) {
                    if let Some(slot) = *slot {
                        if planner.holds[reg].is_none() {
                            planner.request(slot, step, *own, Some(reg));
                        }
                    }
                }
            }
            Step::ExitLive(slots) => {
                for &slot in slots {
                    if planner.pending(slot).is_empty() {
                        planner.request(slot, step, false, None);
                    }
                }
            }
            Step::Thunk => {
                for slot in dirty[step].iter() {
                    if planner.pending(slot).is_empty() {
                        planner.request(slot, step, false, None);
                    }
                }
            }
        }
        planner.cap();
    }
    // At the top, requests for a register are the entry window.
    for reg in 0..WINDOW {
        if let Some(id) = planner.holds[reg].take() {
            planner.keep(id, reg, None);
        }
    }
    planner.drop_pending();

    let mut windows = vec![[None; WINDOW]; steps.len()];
    fn want(windows: &mut [Placement], step: usize, reg: usize, slot: usize) {
        let entry = &mut windows[step][reg];
        assert!(entry.is_none_or(|s| s == slot), "register {reg} wanted for slots {entry:?} and {slot} before step {step}");
        *entry = Some(slot);
    }
    for q in &planner.requests {
        match q.fate {
            Fate::Kept { reg, from } => {
                for step in from.map_or(0, |from| from + 1)..q.at {
                    want(&mut windows, step, reg, q.slot);
                }
            }
            Fate::Home => {}
            Fate::Pending => unreachable!("a request left pending"),
        }
    }
    for (step, s) in steps.iter().enumerate() {
        if let Step::Op(op, _) = s {
            let run = Run { slots: op.operands(), accesses: op.accesses(), skip: skips[step] };
            for (reg, slot, access) in run.operands() {
                if access == Access::Read {
                    want(&mut windows, step, reg, slot);
                }
            }
        }
    }
    // A loop header's entry window has the slots the trace leaves dirty
    // dirty, as its back edge brings them: whichever jump into it is compiled
    // first, or the entry stub, would otherwise fix them clean, and every
    // iteration would store them.
    let dirty = steps
        .iter()
        .zip(&windows)
        .map(|(s, window)| {
            let mut dirty = Slots::default();
            if let Step::Header = s {
                window.iter().flatten().filter(|&&slot| written.contains(slot)).for_each(|&slot| dirty.insert(slot));
            }
            dirty
        })
        .collect();
    TracePlan { windows, skips, dirty, demotions }
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
    fn run_backward(width: usize, ops: &[TestOp]) {
        let windows = windows(ops);
        let steps: Vec<Step> =
            std::iter::once(Step::Start).chain(windows.iter().map(|w| Step::Op(&**w, (0..WINDOW).collect()))).collect();
        let plan = plan_trace(&steps, width);
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
    /// and bottom-up.
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
                run_backward(width, &ops);
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

    /// Random traces of ops over up to six slots, with block and loop starts,
    /// flushes and exits, in windows of 5 to 8 registers, run as the JIT runs
    /// a planned trace: each op reconciled to its planned window, each block
    /// entered through a transfer into its entry window, each exit's transfer
    /// into its target's window checked. Every op reads current values, every
    /// exit delivers its window, and the stack ends current.
    #[test]
    fn random_traces() {
        let mut rng = Rng(0x2545f4914f6cdd1d);
        for _ in 0..3000 {
            let width = 5 + rng.below(4);
            let mut ops = Vec::new();
            let mut kinds = Vec::new();
            for _ in 0..1 + rng.below(24) {
                let k = rng.below(12);
                let header = rng.below(2) == 0;
                let mut slot = || rng.below(6);
                match k {
                    0 if header => kinds.push(5),
                    0 => kinds.push(1),
                    1 => kinds.push(2),
                    2 => kinds.push(3),
                    3 if header => kinds.push(6),
                    3 => kinds.push(4),
                    k => {
                        ops.push(match k {
                            4..=6 => B(slot(), slot(), slot()),
                            7 => TestOp::BinFirst(slot(), slot(), slot()),
                            8 => G(slot(), slot()),
                            9 => S(slot(), slot()),
                            10 => U(slot()),
                            _ => L(slot(), slot(), slot(), slot()),
                        });
                        kinds.push(0);
                    }
                }
            }
            let windows = windows(&ops);
            let mut next_op = windows.iter();
            let steps: Vec<Step> = std::iter::once(Step::Start)
                .chain(kinds.iter().map(|kind| match kind {
                    0 => Step::Op(&**next_op.next().unwrap(), (0..WINDOW).collect()),
                    1 => Step::Start,
                    5 => Step::Header,
                    6 => Step::Thunk,
                    2 => Step::Flush,
                    3 => {
                        let mut window = [None; WINDOW];
                        for reg in window.iter_mut().take(width) {
                            *reg = if rng.below(2) == 1 { Some(rng.below(6)) } else { None };
                        }
                        // A register per slot, as in any window.
                        for reg in 0..WINDOW {
                            if window[..reg].contains(&window[reg]) {
                                window[reg] = None;
                            }
                        }
                        Step::Exit { window, own: rng.below(2) == 0 }
                    }
                    _ => Step::ExitLive((0..rng.below(4)).map(|_| rng.below(6)).collect()),
                }))
                .collect();
            let plan = plan_trace(&steps, width);
            let mut alloc = WindowAlloc::with_width(width);
            let mut machine = Machine::default();
            for (step, s) in steps.iter().enumerate() {
                match s {
                    Step::Start | Step::Header => {
                        let entry = Cache::entry(plan.windows[step], alloc.cache(), &plan.dirty[step]);
                        for emit in alloc.transfer(&entry) {
                            machine.exec(emit, None);
                        }
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
                    Step::Exit { window, .. } => {
                        let mut taken = Machine { memory: machine.memory.clone(), current: machine.current.clone(), regs: machine.regs };
                        for emit in alloc.transfer(&Cache::entry(*window, alloc.cache(), &Slots::default())) {
                            taken.exec(emit, None);
                        }
                        for (reg, slot) in window.iter().enumerate() {
                            if let Some(slot) = *slot {
                                let current = Machine::version(&taken.current, slot);
                                assert_eq!(taken.regs[reg], Some((slot, current)), "exit at step {step} of {ops:?}");
                            }
                        }
                    }
                    Step::ExitLive(_) => {}
                    Step::Thunk => {
                        let mut taken = Machine { memory: machine.memory.clone(), current: machine.current.clone(), regs: machine.regs };
                        for emit in alloc.stores() {
                            taken.exec(emit, None);
                        }
                        for (&slot, &version) in &taken.current {
                            assert_eq!(Machine::version(&taken.memory, slot), version, "slot {slot} stale at the thunk at step {step} of {ops:?}");
                        }
                    }
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
