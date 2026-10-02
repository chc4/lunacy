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
// A trace is planned in two backward passes over its steps: which values are
// in registers, then which registers they are in. Loads and stores are what
// the first minimizes, and moves are the second's only cost, so a value needs
// no one register for as long as it is kept: the window is positional, each op
// taking a run of particular registers, and over a few ops the runs take every
// register in turn. (docs/trace-register-allocation.md)
//
// Residency. Each use requests its slot's value in a register, from its
// source: the op above that writes the slot or reads it, which has it in a
// register. An op's operands need its run's registers, so the requests
// crossing an op must fit in the rest of the window: if they don't, those used
// furthest down are dropped, loaded at their use (and stored where they leave
// the window, if dirty). A value no use requests is dead, and holds nothing,
// unless it is dirty: leaving the window would store it, so it keeps its
// register until the op that writes its slot, which replaces it unstored. It
// never displaces a value the trace itself uses, and is never moved: when its
// register is wanted it is stored, as it would have been. When requests don't
// fit, a pseudo-use of a clean value goes first (at most a load on a side
// exit), then these and the pseudo-uses of dirty values (a store), then the
// trace's own uses. A flush drops every
// request.
//
// The ends of a trace take their uses from the traces around it, as the
// thesis's pseudo-uses and inter-trace hints. An edge leaving the trace into a
// block with an entry window requests that window's slots; into a block with
// none yet, the slots live into it and the dirty ones, which it takes in its
// entry window if it can rather than have them stored on the edge; a jump back
// to a block of the trace, the values the trace reads from that block on
// before writing them; a thunk, the dirty slots. Only the trace's own continuation and its jumps back count as
// its ops' uses do: the others are dropped first. At the trace's top, a
// request is met only if the hint brings its value in a register: the window
// an edge from a trace planned earlier leaves into the head, or that of a
// thunk linked into the region's entry. Otherwise it is loaded at its use.
//
// Loads and stores belong where they run least (the thesis's spill and split
// positions). Where the edge into a block enters more frequent code, by the
// blocks' hotness, or because a later block of the trace jumps back to it (a
// loop runs more often than what enters it, whatever its hotness said when it
// was compiled), the trace's own requests pending there end at the block's
// start, as its entry window, and the code above is asked for them: one it
// can't bring in a register is loaded on that edge rather than in the more
// frequent code. The window has dirty only the slots the trace writes from
// there on, which its own edges into the block bring dirty: any other value
// dirty on the way in is stored on that edge once.
//
// Placement is destination-driven: walking up, each value in a register stays
// where the code below wants it, and each op runs at the usable `SKIP` that
// moves the fewest values, counting an operand the code below wants in
// another register than the run has it in, a value kept across the op whose
// register the run takes (it waits in a free one and moves back), and an
// input its producer in the trace can't write in place. A value nothing below
// wants in a particular register (one live across a jump back, say) has no
// destination: it stays where the code above leaves it until that register is
// needed, then moves to a free one. A forward pre-pass
// finds where each op's output can be produced: the registers it lands in at
// the usable `SKIP`s where the fewest of the op's own inputs miss the places
// their producers can write them. Ties go to the lowest `SKIP`. An edge into a
// block with an entry window wants its values where that window has them.
//
// A trace none of whose steps touches the window, a block of only a thunk or
// only jumps, is the thesis's trivial trace: its blocks are entered with the
// hint as it is, dirty slots and all, and its exits leave it. So a thunk keeps
// the window of the edge into it, for the code compiled once it is forced to
// start from. (The thesis forwards only the values live into the block; what a
// forced thunk's code reads isn't known, so the whole window is forwarded.)

/// A step of a trace, for [`plan_trace`]: its blocks' residuals, as planning
/// sees them.
pub enum Step<'a> {
    /// A block's start. `rise` if the edge into it enters more frequent code.
    Start { rise: bool },
    /// A window op, and the `SKIP`s it can run at.
    Op(&'a dyn Window, SmallVec<[usize; WINDOW]>),
    /// A residual that flushes the window.
    Flush,
    /// An edge leaving the trace into a block entered with `window`: the
    /// trace's continuation if `own`, else a pseudo-use.
    Exit { window: Placement, own: bool },
    /// An edge leaving the trace into a block with no window yet, which these
    /// slots are live into: pseudo-uses, as the slots dirty there are.
    ExitLive(SmallVec<[usize; 16]>),
    /// A jump back to the block starting at step `start`, earlier in the trace.
    Back(usize),
    /// A thunk: an exit to the interpreter, which reads the stack, so the
    /// slots dirty there are pseudo-uses.
    Thunk,
}

/// A planned trace: per step, the placement wanted before it (an op's, or a
/// block's entry window at its `Start`), an op's `SKIP`, at a block's start
/// the slots its entry window is planned dirty, and at an edge leaving the
/// trace or a thunk, the window the plan leaves there. See Note [Trace
/// allocation].
pub struct TracePlan {
    pub windows: Vec<Placement>,
    pub skips: Vec<usize>,
    pub dirty: Vec<Slots>,
    pub exits: Vec<Option<Cache>>,
    /// Whether it is a trivial trace, its blocks entered with the hint as it is.
    pub trivial: bool,
}

/// A use's request for its slot's value in a register. See Note [Trace
/// allocation].
struct Request {
    slot: usize,
    /// The step using it.
    at: usize,
    /// Whether the trace's own code uses it, rather than a pseudo-use.
    own: bool,
    /// Whether it is a dirty value no use reads, kept only until the op at
    /// `at` writes its slot, to save its store.
    spare: bool,
    /// In a register from after step `from` (from the trace's top, if `None`)
    /// to the use, or dropped: loaded at the use.
    kept: Option<Option<usize>>,
}

/// The slots `steps` read before writing them, up to their first flush.
fn exposed(steps: &[Step]) -> Slots {
    let (mut reads, mut written) = (Slots::default(), Slots::default());
    for s in steps {
        match s {
            Step::Op(op, _) => {
                let operands = op.operands().iter().zip(op.accesses());
                operands.clone().filter(|(slot, a)| a.reads() && !written.contains(**slot)).for_each(|(&slot, _)| reads.insert(slot));
                operands.filter(|(_, a)| a.writes()).for_each(|(&slot, _)| written.insert(slot));
            }
            Step::Flush => break,
            _ => {}
        }
    }
    reads
}

/// Which values the trace keeps in registers: each use's request, kept from
/// its source or dropped. `dirty` has, per step, the slots written in the trace
/// since the last flush. See Note [Trace allocation].
fn residency(steps: &[Step], width: usize, hint: &Cache, dirty: &[Slots]) -> Vec<Request> {
    let mut requests: Vec<Request> = Vec::new();
    // The pending requests, one per slot.
    let mut pending: SmallVec<[usize; 16]> = SmallVec::new();
    fn request(requests: &mut Vec<Request>, pending: &mut SmallVec<[usize; 16]>, slot: usize, at: usize, own: bool) {
        if pending.iter().all(|&id| requests[id].slot != slot) {
            pending.push(requests.len());
            requests.push(Request { slot, at, own, spare: false, kept: None });
        }
    }
    // Drop the pending requests `over` holds, beyond `room`: pseudo-uses of
    // values not in `dirty` first (a load on a side exit, at most), then those
    // of dirty values and the spare ones (a store), then the trace's own, each
    // the furthest used first.
    fn shed(requests: &[Request], pending: &mut SmallVec<[usize; 16]>, room: usize, dirty: &Slots, over: impl Fn(&Request) -> bool) {
        let rank = |q: &Request| if q.own { 0 } else if q.spare || dirty.contains(q.slot) { 1 } else { 2 };
        while pending.iter().filter(|&&id| over(&requests[id])).count() > room {
            let victim = pending.iter().copied().filter(|&id| over(&requests[id])).max_by_key(|&id| (rank(&requests[id]), requests[id].at)).expect("a request to drop");
            pending.retain(|&mut id| id != victim);
        }
    }
    for (step, s) in steps.iter().enumerate().rev() {
        match s {
            Step::Start { rise } => {
                if *rise {
                    let ended: SmallVec<[usize; 16]> = pending.iter().copied().filter(|&id| requests[id].own).collect();
                    for id in ended {
                        requests[id].kept = Some(step.checked_sub(1));
                        pending.retain(|&mut p| p != id);
                        let slot = requests[id].slot;
                        request(&mut requests, &mut pending, slot, step, true);
                    }
                }
            }
            Step::Op(op, _) => {
                let (slots, accesses) = (op.operands(), op.accesses());
                shed(&requests, &mut pending, width.saturating_sub(slots.len()), &dirty[step], |q| !slots.contains(&q.slot));
                for &slot in slots {
                    if let Some(at) = pending.iter().position(|&id| requests[id].slot == slot) {
                        let id = pending.remove(at);
                        requests[id].kept = Some(Some(step));
                    }
                }
                for (&slot, _) in slots.iter().zip(accesses).filter(|(_, a)| a.reads()) {
                    request(&mut requests, &mut pending, slot, step, true);
                }
                // The dirty value a write replaces, which nothing reads.
                for (&slot, _) in slots.iter().zip(accesses).filter(|(slot, a)| a.writes() && dirty[step].contains(**slot)) {
                    if pending.iter().all(|&id| requests[id].slot != slot) {
                        pending.push(requests.len());
                        requests.push(Request { slot, at: step, own: false, spare: true, kept: None });
                    }
                }
            }
            Step::Flush => pending.clear(),
            Step::Exit { window, own } => window.iter().take(width).flatten().for_each(|&slot| request(&mut requests, &mut pending, slot, step, *own)),
            Step::ExitLive(slots) => {
                slots.iter().copied().chain(dirty[step].iter()).for_each(|slot| request(&mut requests, &mut pending, slot, step, false));
            }
            Step::Back(start) => exposed(&steps[*start..step]).iter().for_each(|slot| request(&mut requests, &mut pending, slot, step, true)),
            Step::Thunk => dirty[step].iter().for_each(|slot| request(&mut requests, &mut pending, slot, step, false)),
        }
        shed(&requests, &mut pending, width, &dirty[step], |_| true);
    }
    for id in pending {
        if hint.position(requests[id].slot).is_some() {
            requests[id].kept = Some(None);
        }
    }
    requests
}

/// Plan a trace's window ops, walking its `steps` backward, in a window of
/// `width` registers, its head entered from `hint`. See Note [Trace
/// allocation].
pub fn plan_trace(steps: &[Step], width: usize, hint: &Cache) -> TracePlan {
    assert!(width <= WINDOW);
    let leaves = |s: &Step| matches!(s, Step::Exit { .. } | Step::ExitLive(_) | Step::Thunk);
    if steps.iter().all(|s| !matches!(s, Step::Op(..) | Step::Flush)) {
        let mut entry = Cache::default();
        let mut dirty = Slots::default();
        for (reg, slot) in hint.slots() {
            entry.regs[reg] = Some(slot);
            if hint.dirty.contains(&slot) {
                entry.dirty.push(slot);
                dirty.insert(slot);
            }
        }
        return TracePlan {
            windows: vec![entry.regs; steps.len()],
            skips: vec![0; steps.len()],
            dirty: vec![dirty; steps.len()],
            exits: steps.iter().map(|s| leaves(s).then(|| entry.clone())).collect(),
            trivial: true,
        };
    }
    // The slots each step finds dirty: written in the trace since the last
    // flush, or dirty in the hint and not flushed since. And
    // where each op's inputs can be produced in place: the registers their
    // producer in the trace writes them to at the `SKIP`s where its own
    // inputs' producers can (or most can) write those in place in turn, as a
    // mask; any register for an input with no producer in the trace.
    let mut dirty = Vec::with_capacity(steps.len());
    let mut in_place: Vec<SmallVec<[u16; 5]>> = Vec::with_capacity(steps.len());
    let mut written = Slots::default();
    hint.dirty.iter().for_each(|&slot| written.insert(slot));
    // Per slot written since the last flush, the registers its writer can put it in.
    let mut writer: SmallVec<[(usize, u16); 16]> = SmallVec::new();
    // Per block start entered by a rising edge, the slots written since it and
    // since the last flush: those the trace's own edges into it can bring dirty.
    let mut risen: SmallVec<[(usize, Slots); 2]> = SmallVec::new();
    for (step, s) in steps.iter().enumerate() {
        dirty.push(written);
        let mut inputs: SmallVec<[u16; 5]> = SmallVec::new();
        match s {
            Step::Op(op, usable) => {
                let operands = op.operands().iter().zip(op.accesses()).enumerate();
                for (_, (&slot, _)) in operands.clone().filter(|(_, (_, a))| a.reads()) {
                    inputs.push(writer.iter().find(|w| w.0 == slot).map_or(u16::MAX, |w| w.1));
                }
                let reads = |skip: usize| (skip..).zip(op.accesses()).filter(|(_, a)| a.reads()).map(|(reg, _)| reg);
                let misses = |skip: usize| reads(skip).zip(&inputs).filter(|&(reg, mask)| mask & 1 << reg == 0).count();
                let fits = usable.iter().copied().filter(|&skip| skip + op.operands().len() <= width);
                let fewest = fits.clone().map(misses).min().unwrap_or(0);
                let good = fits.filter(|&skip| misses(skip) == fewest).fold(0u16, |mask, skip| mask | 1 << skip);
                for (index, (&slot, _)) in operands.filter(|(_, (_, a))| a.writes()) {
                    written.insert(slot);
                    risen.iter_mut().for_each(|(_, slots)| slots.insert(slot));
                    writer.retain(|w| w.0 != slot);
                    writer.push((slot, good << index));
                }
            }
            Step::Flush => {
                written = Slots::default();
                writer.clear();
                risen.iter_mut().for_each(|(_, slots)| *slots = Slots::default());
            }
            Step::Start { rise: true } => risen.push((step, Slots::default())),
            _ => {}
        }
        in_place.push(inputs);
    }
    // A block entered by a rising edge is entered with the slots the trace
    // writes from there on dirty: they are dirty from its start to the next
    // flush.
    let mut arriving = Slots::default();
    for (step, s) in steps.iter().enumerate() {
        dirty[step].union(&arriving);
        match s {
            Step::Start { rise: true } => risen.iter().filter(|r| r.0 == step).for_each(|r| arriving.union(&r.1)),
            Step::Flush => arriving = Slots::default(),
            _ => {}
        }
    }

    // The slots in registers before each step: those kept across it, and
    // those it uses that were kept up to it.
    let mut resident: Vec<SmallVec<[usize; WINDOW]>> = vec![SmallVec::new(); steps.len()];
    // Per step, the slots in registers only as spare values, with their request.
    let mut spare: Vec<SmallVec<[(usize, usize); 2]>> = vec![SmallVec::new(); steps.len()];
    for (id, q) in residency(steps, width, hint, &dirty).into_iter().enumerate() {
        if let Some(from) = q.kept {
            for step in from.map_or(0, |from| from + 1)..=q.at {
                if !resident[step].contains(&q.slot) {
                    resident[step].push(q.slot);
                    if q.spare {
                        spare[step].push((q.slot, id));
                    }
                }
            }
        }
    }

    // Where the code below wants each value in a register: the register it
    // has it in. A value nothing below wants anywhere is left out, to stay
    // where the code above leaves it.
    let mut below: Placement = [None; WINDOW];
    let mut windows = vec![[None; WINDOW]; steps.len()];
    let mut skips = vec![0; steps.len()];
    for (step, s) in steps.iter().enumerate().rev() {
        let wanted = |slot: usize| below.iter().position(|&s| s == Some(slot));
        let mut window: Placement = [None; WINDOW];
        match s {
            Step::Op(op, usable) => {
                let (slots, accesses) = (op.operands(), op.accesses());
                let crossing = || resident[step].iter().copied().filter(|slot| !slots.contains(slot));
                let moves = |skip: usize| {
                    let run = skip..skip + slots.len();
                    // An operand the code below wants in a register the run
                    // doesn't have it in, once per slot.
                    let mut operands = 0;
                    for (index, &slot) in slots.iter().enumerate() {
                        if slots[..index].contains(&slot) {
                            continue;
                        }
                        let here = (0..slots.len()).filter(|&i| slots[i] == slot).map(|i| skip + i);
                        operands += usize::from(wanted(slot).is_some_and(|reg| here.clone().all(|r| r != reg)));
                    }
                    let displaced = crossing().filter(|&slot| wanted(slot).is_some_and(|reg| run.contains(&reg))).count();
                    let inputs = (skip..).zip(accesses).filter(|(_, a)| a.reads()).map(|(reg, _)| reg);
                    let misplaced = inputs.zip(&in_place[step]).filter(|&(reg, mask)| mask & 1 << reg == 0).count();
                    operands + displaced + misplaced
                };
                let skip = usable.iter().copied().filter(|&skip| skip + slots.len() <= width).min_by_key(|&skip| (moves(skip), skip)).expect("a usable SKIP");
                let run = skip..skip + slots.len();
                for (reg, (&slot, _)) in (skip..).zip(slots.iter().zip(accesses)).filter(|(_, (_, a))| a.reads()) {
                    window[reg] = Some(slot);
                }
                // A value kept across the op stays where it is wanted below,
                // if the run doesn't take that register.
                for slot in crossing() {
                    if let Some(reg) = wanted(slot).filter(|reg| !run.contains(reg)) {
                        window[reg] = Some(slot);
                    }
                }
                skips[step] = skip;
            }
            _ => {
                // An edge into a block with an entry window wants its values
                // where that window has them.
                let target = match s {
                    Step::Exit { window, .. } => *window,
                    _ => [None; WINDOW],
                };
                for &slot in &resident[step] {
                    if let Some(reg) = wanted(slot) {
                        window[reg] = Some(slot);
                    }
                }
                for &slot in resident[step].iter().filter(|&&slot| wanted(slot).is_none()) {
                    if let Some(reg) = target.iter().position(|&s| s == Some(slot)).filter(|&reg| reg < width && window[reg].is_none()) {
                        window[reg] = Some(slot);
                    }
                }
            }
        }
        windows[step] = window;
        below = window;
    }
    // Forward, the values left out: each stays in the register the code above
    // leaves it in (the hint's, at the top), until that register is wanted for
    // another value or taken by an op's run, when it moves to a free one; a
    // spare value is left to be stored instead.
    let mut above: Placement = hint.regs;
    let mut stored: SmallVec<[usize; WINDOW]> = SmallVec::new();
    for (step, s) in steps.iter().enumerate() {
        let run = match s {
            Step::Op(op, _) => skips[step]..skips[step] + op.operands().len(),
            _ => 0..0,
        };
        let window = &mut windows[step];
        let spared = |slot: usize| spare[step].iter().find(|s| s.0 == slot).map(|s| s.1);
        let stays = |window: &Placement, slot: usize| above.iter().position(|&s| s == Some(slot)).filter(|&reg| reg < width && window[reg].is_none() && !run.contains(&reg));
        let left: SmallVec<[usize; WINDOW]> = resident[step].iter().copied().filter(|slot| !window.contains(&Some(*slot))).collect();
        let mut moving: SmallVec<[usize; WINDOW]> = SmallVec::new();
        for &slot in left.iter().filter(|&&slot| spared(slot).is_none()) {
            match stays(window, slot) {
                Some(reg) => window[reg] = Some(slot),
                None => moving.push(slot),
            }
        }
        for slot in moving {
            let free = |reg: &usize| window[*reg].is_none() && !run.contains(reg);
            // A register nothing is in, before one whose value is no longer kept.
            let reg = (0..width).filter(free).find(|&reg| above[reg].is_none()).or_else(|| (0..width).find(free)).expect("room in the window");
            window[reg] = Some(slot);
        }
        // A spare value stays only in a register nothing else took.
        for &slot in &left {
            let Some(id) = spared(slot) else { continue };
            match stays(window, slot).filter(|_| !stored.contains(&id)) {
                Some(reg) => window[reg] = Some(slot),
                None if !stored.contains(&id) => stored.push(id),
                None => {}
            }
        }
        above = *window;
        if let Step::Op(op, _) = s {
            for (reg, (&slot, &access)) in run.clone().zip(op.operands().iter().zip(op.accesses())) {
                if access.writes() {
                    above.iter_mut().filter(|s| **s == Some(slot)).for_each(|s| *s = None);
                    above[reg] = Some(slot);
                }
            }
        }
    }

    let exits = (0..steps.len())
        .map(|step| {
            leaves(&steps[step]).then(|| {
                let regs = windows[step];
                Cache { regs, dirty: dirty[step].iter().filter(|slot| regs.contains(&Some(*slot))).collect() }
            })
        })
        .collect();
    // The entry window of a block entered by a rising edge has the slots the
    // trace writes from there on dirty, as its own edges into the block bring
    // them, and no others.
    let mut dirty = vec![Slots::default(); steps.len()];
    for (step, slots) in risen {
        windows[step].iter().flatten().filter(|&&slot| slots.contains(slot)).for_each(|&slot| dirty[step].insert(slot));
    }
    TracePlan { windows, skips, dirty, exits, trivial: false }
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
            std::iter::once(Step::Start { rise: false }).chain(windows.iter().map(|w| Step::Op(&**w, (0..WINDOW).collect()))).collect();
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
    /// entered by a rising edge), jumps back to them, flushes, thunks and
    /// exits, in windows of 5 to 8 registers, run as the JIT runs a planned
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
                    2 | 3 => kinds.push((3, 0)),
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
            // Any window over `width` registers, some of its slots dirty.
            let some_window = |rng: &mut Rng| {
                let mut window = Cache::default();
                for reg in 0..rng.below(width + 1) {
                    let slot = rng.below(6);
                    if window.position(slot).is_none() {
                        window.regs[reg] = Some(slot);
                        if rng.below(2) == 0 {
                            window.dirty.push(slot);
                        }
                    }
                }
                window
            };
            let steps: Vec<Step> = std::iter::once(Step::Start { rise: false })
                .chain(kinds.iter().map(|&(kind, arg)| match kind {
                    0 => Step::Op(&**next_op.next().unwrap(), (0..WINDOW).collect()),
                    1 => Step::Start { rise: false },
                    2 => Step::Flush,
                    3 => match rng.below(3) {
                        0 => Step::Exit { window: some_window(&mut rng).regs, own: rng.below(2) == 0 },
                        1 => Step::ExitLive((0..rng.below(4)).map(|_| rng.below(6)).collect()),
                        _ => Step::Thunk,
                    },
                    5 => Step::Start { rise: true },
                    _ => Step::Back(arg),
                }))
                .collect();
            let hint = some_window(&mut rng);
            let plan = plan_trace(&steps, width, &hint);
            let mut machine = Machine::default();
            for &slot in &hint.dirty {
                machine.current.insert(slot, 1);
            }
            for (reg, slot) in hint.regs.iter().enumerate() {
                machine.regs[reg] = slot.map(|slot| (slot, Machine::version(&machine.current, slot)));
            }
            let mut alloc = WindowAlloc { width, cache: hint };
            let mut entries = HashMap::new();
            for (step, s) in steps.iter().enumerate() {
                match s {
                    Step::Start { rise } => {
                        let from = if *rise { Cache::default() } else { alloc.cache().clone() };
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
                    Step::Exit { .. } | Step::ExitLive(_) | Step::Thunk => {
                        if let Step::Exit { window, .. } = s {
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
                        let mut taken = Machine { memory: machine.memory.clone(), current: machine.current.clone(), regs: machine.regs };
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
                        let trivial = plan_trace(&[Step::Start { rise: false }], width, plan.exits[step].as_ref().unwrap());
                        let entry = Cache::entry(trivial.windows[0], alloc.cache(), &trivial.dirty[0]);
                        let mut linked = Machine { memory: machine.memory.clone(), current: machine.current.clone(), regs: machine.regs };
                        for emit in alloc.transfer(&entry) {
                            linked.exec(emit, None);
                        }
                        let thunk = WindowAlloc { width, cache: entry };
                        let mut exited = Machine { memory: linked.memory.clone(), current: linked.current.clone(), regs: linked.regs };
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
                        for (reg, slot) in target.regs.iter().enumerate() {
                            if let Some(slot) = *slot {
                                let current = Machine::version(&linked.current, slot);
                                assert_eq!(linked.regs[reg], Some((slot, current)), "link after step {step} of {ops:?} into {target:?}");
                            }
                        }
                        for (&slot, &version) in linked.current.iter().filter(|(slot, _)| !target.dirty.contains(slot)) {
                            assert_eq!(Machine::version(&linked.memory, slot), version, "slot {slot} lost by the link after step {step} of {ops:?} into {target:?}");
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

    /// A trivial trace, a block of only a thunk or only a jump, is entered with
    /// the hint as it is and leaves it along its exit, whether or not the edge
    /// into it enters more frequent code.
    #[test]
    fn trivial_trace_forwards_its_hint() {
        let mut hint = Cache::default();
        hint.regs[1] = Some(4);
        hint.regs[3] = Some(2);
        hint.dirty.push(2);
        for steps in [vec![Step::Start { rise: false }], vec![Step::Start { rise: true }], vec![Step::Start { rise: false }, Step::ExitLive(SmallVec::new())]] {
            let plan = plan_trace(&steps, WINDOW, &hint);
            assert!(plan.trivial);
            assert_eq!(plan.windows[0], hint.regs);
            assert_eq!(plan.dirty[0].iter().collect::<Vec<_>>(), vec![2]);
            if steps.len() > 1 {
                assert_eq!(plan.exits[1].as_ref(), Some(&hint));
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
