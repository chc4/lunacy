//! Register allocation for window ops in the JIT: which window register caches
//! which stack slot, decided op by op in one forward pass. See Note [Register
//! window] and Note [Window allocation].

use smallvec::SmallVec;

use crate::window::{Access, Gpr, Window, WINDOW};

// Note [Window allocation]
// ~~~~~~~~~~~~~~~~~~~~~~~~
// A streaming allocator, like copy-and-patch's (Xu & Kjolstad, OOPSLA 2021): one
// forward pass during codegen, a few register comparisons per op, no lookahead
// and no liveness. Each register caches at most one slot's current value, and a
// cached slot is dirty while its stack home is stale. `Storage` only records its
// token. At an `ExecWindow` the op runs at the usable `SKIP` whose resculpt of
// `w[SKIP..]` emits least, at `MEMORY_COST` per load or store and `MOVE_COST`
// per register move:
//
// * an input already in its register costs nothing, one cached in another
//   register a move, and an uncached one a load (a repeated input copies its
//   first use);
// * a dirty value the op's run overwrites is stored first, unless it survives
//   elsewhere (in another register, or as one of the op's inputs) or the op
//   rewrites its slot.
//
// Ties go to the `SKIP` that overwrites the fewest cached values, then to the
// lowest. An overwritten clean value is dropped, and a later read reloads it.
// Any other residual ends the run and flushes every dirty register.

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

impl Emit {
    fn cost(self) -> u32 {
        match self {
            Emit::Load { .. } | Emit::Store { .. } => MEMORY_COST,
            Emit::Move { .. } => MOVE_COST,
            Emit::Op { .. } => 0,
        }
    }
}

/// The window's cache between window residuals.
#[derive(Debug, Clone, Default)]
struct Cache {
    /// The slot whose current value each register holds.
    regs: [Option<usize>; WINDOW],
    /// Cached slots whose stack home is stale.
    dirty: SmallVec<[usize; WINDOW]>,
}

impl Cache {
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
    /// Tokens recorded by `Storage` since the last op.
    pending: SmallVec<[(Gpr, Access); WINDOW]>,
}

impl Default for WindowAlloc {
    fn default() -> Self {
        Self::with_width(WINDOW)
    }
}

impl WindowAlloc {
    fn with_width(width: usize) -> Self {
        assert!(width <= WINDOW);
        WindowAlloc { width, cache: Cache::default(), pending: SmallVec::new() }
    }

    /// Whether no register holds a value and no token is pending.
    pub fn is_empty(&self) -> bool {
        self.pending.is_empty() && self.cache.regs.iter().all(Option::is_none)
    }

    /// A `Storage` of the run.
    pub fn storage(&mut self, gpr: Gpr, access: Access) {
        self.pending.push((gpr, access));
    }

    /// The next op of the run: resculpt the window for it at the cheapest of the
    /// `skips` it can run at, and run it. `None` if there are none.
    pub fn op(&mut self, op: &dyn Window, skips: impl IntoIterator<Item = usize>) -> Option<SmallVec<[Emit; 16]>> {
        let name = op.name();
        let accesses = op.accesses();
        assert_eq!(self.pending.len(), op.operands().len(), "{name}: operands without a Storage");
        for (i, ((gpr, access), operand)) in self.pending.iter().zip(op.operands()).enumerate() {
            assert_eq!(gpr, operand, "{name}: operand {i} is not the token of its Storage");
            assert_eq!(*access, accesses[i], "{name}: operand {i} was stored as {access:?}");
        }
        self.pending.clear();
        let slots: SmallVec<[usize; WINDOW]> = op.operands().iter().map(|gpr| gpr.slot()).collect();
        let plan = skips
            .into_iter()
            .filter(|&skip| skip + slots.len() <= self.width)
            .map(|skip| self.plan(&slots, accesses, skip))
            .min_by_key(|plan| (plan.cost, plan.overwritten, plan.skip))?;
        self.cache = plan.after;
        Some(plan.emits)
    }

    /// End the run: flush every dirty register.
    pub fn flush(&mut self) -> SmallVec<[Emit; WINDOW]> {
        assert!(self.pending.is_empty(), "a window run ended between a Storage and its op");
        let cache = core::mem::take(&mut self.cache);
        cache
            .dirty
            .iter()
            .map(|&slot| Emit::Store { slot, reg: cache.position(slot).expect("dirty slot in a register") })
            .collect()
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
        sequentialize(&mut moves, &mut emits);
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

/// Emit the parallel assignment `moves` (distinct destinations) as a sequence,
/// breaking cycles through `SCRATCH`.
fn sequentialize(moves: &mut SmallVec<[(usize, Source); 8]>, emits: &mut SmallVec<[Emit; 16]>) {
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
                // Every destination is still read: a cycle. Park one in SCRATCH.
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
    use crate::window::{windowed, Tokens};
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
                    for (i, (gpr, _)) in operands.clone().filter(|(_, (_, a))| **a == Access::Read) {
                        let current = Self::version(&self.current, gpr.slot());
                        assert_eq!(self.regs[skip + i], Some((gpr.slot(), current)), "input {i} of {op:?}");
                    }
                    for (i, (gpr, _)) in operands.filter(|(_, (_, a))| **a == Access::Write) {
                        let version = Self::version(&self.current, gpr.slot()) + 1;
                        self.current.insert(gpr.slot(), version);
                        self.regs[skip + i] = Some((gpr.slot(), version));
                    }
                }
            }
        }
    }

    /// Allocate and execute a run in a window of `width` registers, returning
    /// the machine for its counts.
    fn run(width: usize, ops: &[TestOp]) -> Machine {
        let mut t = Tokens::default();
        let windows: Vec<Box<dyn Window>> = ops
            .iter()
            .map(|op| -> Box<dyn Window> {
                match *op {
                    TestOp::Bin(a, b, d) => Box::new(Bin::new(&[t.mint(a), t.mint(b), t.mint(d)])),
                    TestOp::BinFirst(a, b, d) => Box::new(BinFirst::new(&[t.mint(d), t.mint(a), t.mint(b)])),
                    TestOp::Get(a, d) => Box::new(Get::new(&[t.mint(a), t.mint(d)])),
                    TestOp::Set(a, b) => Box::new(Set::new(&[t.mint(a), t.mint(b)])),
                    TestOp::Out(d) => Box::new(Out::new(&[t.mint(d)])),
                    TestOp::Loop(i, l, s, v) => Box::new(Loop::new(&[t.mint(i), t.mint(l), t.mint(s), t.mint(v), t.mint(v)])),
                }
            })
            .collect();
        let mut alloc = WindowAlloc::with_width(width);
        let mut machine = Machine::default();
        for w in &windows {
            for (gpr, access) in w.operands().iter().zip(w.accesses()) {
                alloc.storage(*gpr, *access);
            }
            for emit in alloc.op(&**w, 0..WINDOW).unwrap() {
                machine.exec(emit, Some(&**w));
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
    /// its widest op), so that the runs overwrite dirty values.
    #[test]
    fn exhaustive_small_runs() {
        let arity = |op: &TestOp| match op {
            TestOp::Bin(..) | TestOp::BinFirst(..) => 3,
            TestOp::Get(..) | TestOp::Set(..) => 2,
            TestOp::Out(..) => 1,
            TestOp::Loop(..) => 5,
        };
        let shapes = [B(0, 0, 0), TestOp::BinFirst(0, 0, 0), G(0, 0), S(0, 0), U(0), L(0, 0, 0, 0)];
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
                        TestOp::Out(..) => U(next()),
                        TestOp::Loop(..) => L(next(), next(), next(), next()),
                    })
                    .collect();
                run(ops.iter().map(arity).max().unwrap().max(4), &ops);
            }
        }
    }

    /// Cycles between registers are broken through `SCRATCH`.
    #[test]
    fn sequentialize_cycle() {
        let mut moves: SmallVec<[(usize, Source); 8]> =
            SmallVec::from_slice(&[(0, Source::Reg(1)), (1, Source::Reg(0)), (2, Source::Memory(7))]);
        let mut emits = SmallVec::new();
        sequentialize(&mut moves, &mut emits);
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
