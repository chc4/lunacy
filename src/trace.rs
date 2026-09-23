//! Traces over a compiled region, and the liveness of stack slots across it,
//! for the window allocator. See Note [Trace register allocation].

use smallvec::SmallVec;

// Note [Trace register allocation]
// ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// The window allocator follows trace register allocation (Eisl, "Trace Register
// Allocation", 2018; docs/trace-register-allocation.md). A compiled region's
// blocks are partitioned into traces: sequences of blocks where each is a
// successor of the one before it, joined by forward edges (not retreating edges
// of the region's depth-first walk). Building the partition is a policy
// (`Policy`); allocation is correct for any partition. Each trace is then
// allocated by one backward pass, with the slot liveness computed here, and
// every edge other than one between consecutive blocks of a trace is resolved
// at its jump.
//
// Liveness is of stack slots in the window's sense: a slot is live at a point
// if a later read in the region can take its value from a register, so a flush
// point, after which everything is loaded from the stack, ends every live range.
// It is one backward pass over the region in postorder, then for each loop (a
// retreating edge whose target dominates its source) adding what is live into
// the loop's header to every block of the loop. Slots aren't SSA values, so a
// slot redefined inside a loop is marked live across all of it: an
// over-approximation, which costs only register pressure since every slot has
// its stack home. A region with a retreating edge whose target doesn't
// dominate its source is irreducible; every block of it gets every slot the
// region reads, or that a block outside it wants in a register.

/// What a block does with stack slots and control flow, in order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    /// A window read of the slot.
    Read(usize),
    /// A window write of the slot.
    Write(usize),
    /// A residual that clobbers the window or reads the stack.
    Flush,
    /// An edge to the region's block with this index.
    Edge(usize),
    /// An edge leaving the region, to a block compiled already, which wants
    /// these slots in registers.
    Exit(Slots),
}

/// A block of a region: its events, and its hotness (the countdown to
/// compilation, lower is hotter) and id, which order blocks by frequency.
#[derive(Debug, Clone)]
pub struct Block {
    pub events: Vec<Event>,
    pub hotness: usize,
    pub id: usize,
}

/// A set of stack slots. A Lua frame has at most 250.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Slots([u64; 4]);

impl Slots {
    pub fn insert(&mut self, slot: usize) {
        assert!(slot < 256, "a frame slot below 256");
        self.0[slot / 64] |= 1 << (slot % 64);
    }

    pub fn remove(&mut self, slot: usize) {
        self.0[slot / 64] &= !(1 << (slot % 64));
    }

    pub fn contains(&self, slot: usize) -> bool {
        slot < 256 && self.0[slot / 64] & (1 << (slot % 64)) != 0
    }

    pub fn union(&mut self, other: &Slots) {
        for (a, b) in self.0.iter_mut().zip(other.0) {
            *a |= b;
        }
    }

    /// Whether every slot in `other` is in `self`.
    pub fn covers(&self, other: &Slots) -> bool {
        self.0.iter().zip(other.0).all(|(a, b)| b & !a == 0)
    }

    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        (0..256).filter(|&slot| self.contains(slot))
    }
}

/// A region's blocks, the entry at index 0, with the edges between them.
pub struct Region {
    pub blocks: Vec<Block>,
    succs: Vec<SmallVec<[usize; 2]>>,
    preds: Vec<SmallVec<[usize; 2]>>,
    /// Blocks in postorder of the depth-first walk from the entry.
    postorder: Vec<usize>,
    /// The retreating edges of that walk: to a block still on its stack.
    retreating: Vec<(usize, usize)>,
}

impl Region {
    /// The region of `blocks`, each reachable from the first.
    pub fn new(blocks: Vec<Block>) -> Region {
        let n = blocks.len();
        let mut succs: Vec<SmallVec<[usize; 2]>> = vec![SmallVec::new(); n];
        for (b, block) in blocks.iter().enumerate() {
            for event in &block.events {
                if let Event::Edge(target) = *event {
                    assert!(target < n, "an edge to a block of the region");
                    if !succs[b].contains(&target) {
                        succs[b].push(target);
                    }
                }
            }
        }
        let mut preds: Vec<SmallVec<[usize; 2]>> = vec![SmallVec::new(); n];
        for (b, targets) in succs.iter().enumerate() {
            for &target in targets {
                preds[target].push(b);
            }
        }
        // Depth-first walk: 0 unvisited, 1 on the stack, 2 finished.
        let mut state = vec![0u8; n];
        let mut postorder = Vec::with_capacity(n);
        let mut retreating = Vec::new();
        let mut stack = vec![(0, 0)];
        state[0] = 1;
        while let Some((b, next)) = stack.last_mut() {
            let b = *b;
            match succs[b].get(*next).copied() {
                Some(target) => {
                    *next += 1;
                    match state[target] {
                        0 => {
                            state[target] = 1;
                            stack.push((target, 0));
                        }
                        1 => retreating.push((b, target)),
                        _ => {}
                    }
                }
                None => {
                    state[b] = 2;
                    postorder.push(b);
                    stack.pop();
                }
            }
        }
        assert_eq!(postorder.len(), n, "every block reachable from the entry");
        Region { blocks, succs, preds, postorder, retreating }
    }

    pub fn succs(&self, b: usize) -> &[usize] {
        &self.succs[b]
    }

    pub fn postorder(&self) -> &[usize] {
        &self.postorder
    }

    pub fn is_retreating(&self, from: usize, to: usize) -> bool {
        self.retreating.contains(&(from, to))
    }

    /// Whether every path from the entry to `b` passes through `d`.
    fn dominates(&self, d: usize, b: usize) -> bool {
        if d == 0 || d == b {
            return true;
        }
        let mut seen = vec![false; self.blocks.len()];
        seen[d] = true;
        seen[0] = true;
        let mut work = vec![0];
        while let Some(x) = work.pop() {
            if x == b {
                return false;
            }
            for &s in &self.succs[x] {
                if !seen[s] {
                    seen[s] = true;
                    work.push(s);
                }
            }
        }
        true
    }

    /// The slots live into each block. See Note [Trace register allocation].
    pub fn liveness(&self) -> Vec<Slots> {
        let n = self.blocks.len();
        let mut live_in = vec![Slots::default(); n];
        for &b in &self.postorder {
            let computed = block_live_in(&self.blocks[b].events, |t| live_in[t]);
            live_in[b] = computed;
        }
        if self.retreating.iter().any(|&(s, h)| !self.dominates(h, s)) {
            let mut every = Slots::default();
            for block in &self.blocks {
                for event in &block.events {
                    match event {
                        Event::Read(slot) => every.insert(*slot),
                        Event::Exit(slots) => every.union(slots),
                        _ => {}
                    }
                }
            }
            return vec![every; n];
        }
        for &(latch, header) in &self.retreating {
            let carried = live_in[header];
            // The loop: the header, and every block reaching the latch without
            // passing through the header.
            let mut in_loop = vec![false; n];
            in_loop[header] = true;
            let mut work = Vec::new();
            if !in_loop[latch] {
                in_loop[latch] = true;
                work.push(latch);
            }
            while let Some(b) = work.pop() {
                live_in[b].union(&carried);
                for &p in &self.preds[b] {
                    if !in_loop[p] {
                        in_loop[p] = true;
                        work.push(p);
                    }
                }
            }
        }
        live_in
    }
}

/// The slots live into a block with `events`, given what is live into its
/// successors.
pub fn block_live_in(events: &[Event], live_in: impl Fn(usize) -> Slots) -> Slots {
    let mut live = Slots::default();
    for event in events.iter().rev() {
        match event {
            Event::Read(slot) => live.insert(*slot),
            Event::Write(slot) => live.remove(*slot),
            Event::Flush => live = Slots::default(),
            Event::Edge(target) => live.union(&live_in(*target)),
            Event::Exit(slots) => live.union(slots),
        }
    }
    live
}

/// How a region is partitioned into traces. See docs/trace-register-allocation.md.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Policy {
    /// Every block its own trace, allocated in postorder.
    SingleBlock,
    /// Start at a block whose predecessors are all in traces (at first the
    /// entry; the most frequent otherwise), and append the most frequent
    /// successor not in a trace until there is none.
    Unidirectional,
    /// Start at the most frequent block not in a trace, prepend its most
    /// frequent predecessor not in a trace until there is none, then append as
    /// `Unidirectional`.
    Bidirectional,
}

impl Policy {
    /// The policy named by `LUNACY_TRACES` (`single`, `unidirectional` or
    /// `bidirectional`), unidirectional if unset.
    pub fn from_env() -> Policy {
        match std::env::var("LUNACY_TRACES").as_deref() {
            Ok("single") => Policy::SingleBlock,
            Ok("bidirectional") => Policy::Bidirectional,
            Ok("unidirectional") | Err(_) => Policy::Unidirectional,
            Ok(other) => panic!("LUNACY_TRACES: no trace policy {other:?}"),
        }
    }
}

impl Region {
    /// The region's traces, in the order they are allocated.
    pub fn traces(&self, policy: Policy) -> Vec<Vec<usize>> {
        let n = self.blocks.len();
        let hotter = |b: usize| (self.blocks[b].hotness, self.blocks[b].id);
        let mut placed = vec![false; n];
        let mut traces = Vec::new();
        if policy == Policy::SingleBlock {
            return self.postorder.iter().map(|&b| vec![b]).collect();
        }
        while let Some(fallback) = (0..n).filter(|&b| !placed[b]).min_by_key(|&b| hotter(b)) {
            let start = match policy {
                Policy::Unidirectional if traces.is_empty() => 0,
                Policy::Unidirectional => (0..n)
                    .filter(|&b| !placed[b] && self.preds[b].iter().all(|&p| placed[p]))
                    .min_by_key(|&b| hotter(b))
                    .unwrap_or(fallback),
                _ => fallback,
            };
            placed[start] = true;
            let mut trace = std::collections::VecDeque::from([start]);
            if policy == Policy::Bidirectional {
                let mut head = start;
                while let Some(p) = self.preds[head]
                    .iter()
                    .copied()
                    .filter(|&p| !placed[p] && !self.is_retreating(p, head))
                    .min_by_key(|&p| hotter(p))
                {
                    placed[p] = true;
                    trace.push_front(p);
                    head = p;
                }
            }
            let mut last = start;
            while let Some(s) =
                self.succs[last].iter().copied().filter(|&s| !placed[s] && !self.is_retreating(last, s)).min_by_key(|&s| hotter(s))
            {
                placed[s] = true;
                trace.push_back(s);
                last = s;
            }
            traces.push(trace.into());
        }
        traces
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A block reading, writing and jumping as `events` say, with hotness 0 and
    /// its index as its id unless `hot` says otherwise.
    fn region(blocks: &[&[Event]], hot: &[(usize, usize)]) -> Region {
        Region::new(
            blocks
                .iter()
                .enumerate()
                .map(|(b, events)| {
                    let hotness = hot.iter().find(|(x, _)| *x == b).map_or(0, |&(_, h)| h);
                    Block { events: events.to_vec(), hotness, id: b }
                })
                .collect(),
        )
    }

    use Event::{Edge as E, Flush as F, Read as R, Write as W};

    const POLICIES: [Policy; 3] = [Policy::SingleBlock, Policy::Unidirectional, Policy::Bidirectional];

    /// The invariants every policy upholds: the traces partition the region,
    /// consecutive blocks of a trace are joined by a forward edge, and the
    /// greedy policies can't extend any trace further.
    fn check(region: &Region, policy: Policy) -> Vec<Vec<usize>> {
        let traces = region.traces(policy);
        let n = region.blocks.len();
        let mut trace_of = vec![usize::MAX; n];
        for (t, trace) in traces.iter().enumerate() {
            assert!(!trace.is_empty(), "{policy:?}: an empty trace");
            for &b in trace {
                assert_eq!(trace_of[b], usize::MAX, "{policy:?}: block {b} in two traces: {traces:?}");
                trace_of[b] = t;
            }
            for pair in trace.windows(2) {
                assert!(region.succs(pair[0]).contains(&pair[1]), "{policy:?}: {pair:?} isn't an edge: {traces:?}");
                assert!(!region.is_retreating(pair[0], pair[1]), "{policy:?}: {pair:?} retreats: {traces:?}");
            }
        }
        assert!(trace_of.iter().all(|&t| t != usize::MAX), "{policy:?}: a block in no trace: {traces:?}");
        match policy {
            Policy::SingleBlock => {
                assert!(traces.iter().all(|trace| trace.len() == 1));
                assert_eq!(traces.iter().map(|trace| trace[0]).collect::<Vec<_>>(), region.postorder());
            }
            Policy::Unidirectional | Policy::Bidirectional => {
                for (t, trace) in traces.iter().enumerate() {
                    let last = *trace.last().unwrap();
                    for &s in region.succs(last) {
                        assert!(
                            region.is_retreating(last, s) || trace_of[s] <= t,
                            "{policy:?}: trace {t} could go on to {s}: {traces:?}"
                        );
                    }
                }
                if policy == Policy::Unidirectional {
                    assert_eq!(traces[0][0], 0, "the first trace starts at the entry");
                } else {
                    for (t, trace) in traces.iter().enumerate() {
                        let head = trace[0];
                        for &p in &region.preds[head] {
                            assert!(
                                region.is_retreating(p, head) || trace_of[p] <= t,
                                "{policy:?}: trace {t} could start at {p}: {traces:?}"
                            );
                        }
                    }
                }
            }
        }
        traces
    }

    /// Liveness by iterating the blocks' transfer to a fixpoint.
    fn fixpoint(region: &Region) -> Vec<Slots> {
        let n = region.blocks.len();
        let mut live_in = vec![Slots::default(); n];
        loop {
            let mut changed = false;
            for b in 0..n {
                let computed = block_live_in(&region.blocks[b].events, |t| live_in[t]);
                if computed != live_in[b] {
                    live_in[b] = computed;
                    changed = true;
                }
            }
            if !changed {
                return live_in;
            }
        }
    }

    /// The region's liveness covers the exact one, and is exact without cycles.
    fn check_liveness(region: &Region) {
        let live = region.liveness();
        let exact = fixpoint(region);
        for b in 0..region.blocks.len() {
            assert!(live[b].covers(&exact[b]), "block {b}: {:?} misses some of {:?}", live[b], exact[b]);
        }
        if region.retreating.is_empty() {
            assert_eq!(live, exact);
        }
    }

    #[test]
    fn straight_line_is_one_trace() {
        let r = region(&[&[R(1), E(1)], &[W(2), E(2)], &[R(2), E(3)], &[]], &[]);
        for policy in [Policy::Unidirectional, Policy::Bidirectional] {
            assert_eq!(check(&r, policy), vec![vec![0, 1, 2, 3]]);
        }
        check(&r, Policy::SingleBlock);
        check_liveness(&r);
        let live = r.liveness();
        assert!(live[0].contains(1) && !live[0].contains(2) && live[2].contains(2));
    }

    #[test]
    fn diamond_follows_the_hotter_arm() {
        // 0 branches to 1 (cold) and 2 (hot), both joining at 3: the edges
        // into 3 are critical.
        let r = region(&[&[E(1), E(2)], &[E(3)], &[E(3)], &[R(5)]], &[(1, 40)]);
        assert_eq!(check(&r, Policy::Unidirectional), vec![vec![0, 2, 3], vec![1]]);
        for policy in POLICIES {
            check(&r, policy);
        }
        check_liveness(&r);
        assert!(r.liveness()[1].contains(5));
    }

    #[test]
    fn a_critical_edge_can_skip_inside_a_trace() {
        // 0 jumps to 1 and to 2; 1 falls through to 2. The trace 0, 1, 2 has
        // the forward edge 0 -> 2 skipping 1, resolved at its jump.
        let r = region(&[&[E(1), E(2)], &[E(2)], &[]], &[]);
        assert_eq!(check(&r, Policy::Unidirectional), vec![vec![0, 1, 2]]);
        check_liveness(&r);
    }

    #[test]
    fn loop_ends_its_trace_at_the_back_edge() {
        // 0 enters the loop 1 -> 2 -> 3 -> 1, which exits from 1 to 4.
        let r = region(&[&[E(1)], &[R(1), E(2), E(4)], &[W(1), E(3)], &[E(1)], &[]], &[(4, 30)]);
        let traces = check(&r, Policy::Unidirectional);
        assert_eq!(traces[0], vec![0, 1, 2, 3]);
        assert!(r.is_retreating(3, 1));
        for policy in POLICIES {
            check(&r, policy);
        }
        check_liveness(&r);
        // Slot 1 is written in 2 and read in the header across the back edge.
        let live = r.liveness();
        assert!(live[3].contains(1));
        assert!(live[0].contains(1));
    }

    #[test]
    fn region_entered_inside_its_loop() {
        // The region's entry is the middle of the loop 0 -> 1 -> 2 -> 0, the
        // block whose hotness triggered compilation, and the loop exits at 1.
        let r = region(&[&[R(3), E(1)], &[E(2), E(3)], &[W(3), E(0)], &[]], &[(3, 50)]);
        for policy in POLICIES {
            check(&r, policy);
        }
        assert_eq!(check(&r, Policy::Unidirectional)[0], vec![0, 1, 2]);
        check_liveness(&r);
    }

    #[test]
    fn nested_loops() {
        // 0 -> 1 (outer header) -> 2 (inner header) -> 3 -> 2, 2 -> 4 -> 1, 1 -> 5.
        let r = region(
            &[&[E(1)], &[R(7), E(2), E(5)], &[R(8), E(3), E(4)], &[W(8), E(2)], &[W(7), E(1)], &[]],
            &[(4, 10), (5, 60)],
        );
        for policy in POLICIES {
            check(&r, policy);
        }
        check_liveness(&r);
        let live = r.liveness();
        // The inner loop carries 8 and passes the outer loop's 7 through.
        assert!(live[3].contains(8) && live[3].contains(7));
    }

    #[test]
    fn self_loop() {
        let r = region(&[&[E(1)], &[R(2), W(2), E(1), E(2)], &[]], &[]);
        for policy in POLICIES {
            check(&r, policy);
        }
        assert!(r.is_retreating(1, 1));
        check_liveness(&r);
        assert!(r.liveness()[1].contains(2));
    }

    #[test]
    fn a_flush_ends_live_ranges() {
        let r = region(&[&[W(1), E(1)], &[F, R(1)]], &[]);
        check_liveness(&r);
        assert_eq!(r.liveness()[1], Slots::default());
    }

    #[test]
    fn irreducible_loop() {
        // 0 enters the cycle 1 <-> 2 at both 1 and 2.
        let r = region(&[&[E(1), E(2)], &[R(4), E(2)], &[R(5), E(1), E(3)], &[R(6)]], &[]);
        for policy in POLICIES {
            check(&r, policy);
        }
        check_liveness(&r);
        let live = r.liveness();
        for b in 0..4 {
            assert!([4, 5, 6].iter().all(|&slot| live[b].contains(slot)));
        }
    }

    /// A xorshift generator, for reproducible random regions.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: usize) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % n as u64) as usize
        }
    }

    /// Random regions of up to 9 blocks and 6 slots: every block reachable
    /// through a spanning chain, plus random edges (back edges, self-loops,
    /// critical edges and irreducible cycles among them), random reads,
    /// writes and flushes, and random hotness. Every policy's traces uphold
    /// the invariants, and liveness covers the exact one.
    #[test]
    fn random_regions() {
        let mut rng = Rng(0x9e3779b97f4a7c15);
        let mut irreducible = 0;
        for _ in 0..3000 {
            let n = 1 + rng.below(9);
            let blocks: Vec<Block> = (0..n)
                .map(|b| {
                    let mut events = Vec::new();
                    for _ in 0..rng.below(5) {
                        events.push(match rng.below(4) {
                            0 => Event::Read(rng.below(6)),
                            1 => Event::Write(rng.below(6)),
                            2 if rng.below(3) == 0 => Event::Flush,
                            _ => Event::Read(rng.below(6)),
                        });
                    }
                    for _ in 0..rng.below(3) {
                        events.push(Event::Edge(rng.below(n)));
                    }
                    Block { events, hotness: rng.below(3) * 20, id: b }
                })
                .collect();
            // The spanning tree: every block's parent jumps to it somewhere.
            let mut blocks = blocks;
            for b in 1..n {
                let parent = rng.below(b);
                let at = rng.below(blocks[parent].events.len() + 1);
                blocks[parent].events.insert(at, Event::Edge(b));
            }
            let r = Region::new(blocks);
            if r.retreating.iter().any(|&(s, h)| !r.dominates(h, s)) {
                irreducible += 1;
            }
            for policy in POLICIES {
                check(&r, policy);
            }
            check_liveness(&r);
        }
        assert!(irreducible > 100, "the random regions include irreducible ones ({irreducible})");
    }
}
