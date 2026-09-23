# Trace register allocation for the window (proposal)

A proposal to base the window allocator on trace register allocation (Josef
Eisl, *Trace Register Allocation*, JKU Linz 2018; built for Graal), replacing
the per-block backward planning, whose rules for what a displaced value costs
and what a block's entry window holds have no model behind them.

## The model

The thesis separates what a trace is from how traces are built: the allocation
works on any partition into traces, and building them is a policy, of which it
evaluates two and names a third.

- **Traces.** The control-flow graph is partitioned into traces: sequences of
  blocks where each block's successor in the trace is one of its CFG
  successors, and no edge inside a trace is a back edge. Every block is in
  exactly one trace. Every other edge is an edge between traces, into another
  trace's head or middle.
- **Trace building**, a policy producing a partition and the order its traces
  are allocated in (see Trace building policies below). The thesis prefers the
  unidirectional builder, and notes that with every block its own trace, trace
  register allocation is local register allocation.
- **Global liveness**, computed once: `live_in` and `live_out` per block. A
  block's `live_out` is a pseudo-use at its end, keeping values alive for the
  traces that branch off it; a trace head's `live_in` is a pseudo-definition.
  It is one backward pass over the blocks in reverse postorder, plus, for each
  loop, adding what is live into its header to every block of the loop
  (Wimmer and Franz 2010). No fixpoint: in SSA form a value live at a loop
  header can't be killed inside the loop. Inside a trace, liveness has no
  holes, since a trace is a straight line.
- **Allocation, one trace at a time**, in the policy's order, most important
  first. The bottom-up
  strategy is one backward pass over a trace with a map from registers to
  variables and from variables to locations: per instruction, its outputs first
  (their registers become free), then its inputs (where they already are, else
  a free register, else the first register the instruction doesn't use,
  evicted, with a reload after the instruction). It starts from the entry
  locations of an already allocated successor. It deliberately doesn't try
  harder (furthest-first eviction, delayed spill stores, round-robin registers
  were all tried and dropped for compile time).
- **Resolution.** Each trace records where its boundary values are; every edge
  between traces gets the parallel moves between the two, and a loop's back
  edge, which is always the end of a trace, is resolved the same way.

## Mapped onto the window

**Blocks and exits.** An LBBV block is already an extended basic block: a
straight line whose guards branch off it. A guard's failure edge is either its
thunk, an exit to the interpreter where the dirty registers are stored, or,
once the thunk is forced, a jump to another block, an edge between traces. A
select's targets are edges too. Which of these edges join blocks of one trace
is up to the building policy. Under a policy following frequent successors, a
chain of small blocks joined by jumps, like life's neighbour-count loop, is one
trace allocated in one backward pass; with single-block traces, every jump is
an edge between traces, reconciled like the per-block planning did.

**Liveness of slots.** Variables are stack slots, not SSA values: a slot can be
redefined inside a loop. The single pass with loop-header propagation then
over-approximates, marking a slot live across a loop that redefines it. That is
safe here: every slot has its stack home, so a slot wrongly thought live costs
only register pressure, never correctness. A Lua frame has at most 250 slots,
so a live set is a 256-bit set per block. Exits to the interpreter and flush
points need nothing in registers; since the interpreter may read any slot
after an exit, liveness never removes a store of a dirty value, only decides
which values are worth a register.

The loop step assumes a reducible region, where a loop's header dominates its
blocks. Lua 5.1 bytecode has no `goto`, so its control flow is reducible, but
block versioning isn't bound by that: if two paths reach a loop in different
contexts and join the steady-state loop's versions at different blocks, that
loop has two entries. The liveness pass checks that the target of each
retreating edge of its depth-first walk dominates the edge's source, and where
one doesn't, it treats every slot as live in the blocks of that cycle.

**Allocating a trace.** One backward pass with the wanted window (which slot
each register should hold) as the register-to-variable map; a slot not in it
is in its stack home. At a window op:

1. its outputs are removed from the window (their old values are dead before
   it, unless also inputs);
2. it is placed at the usable `SKIP` that displaces the fewest wanted values
   from its run and lands the most outputs where they are wanted, ties to the
   lowest: the window's constraint that an op's operands are a contiguous run
   replaces choosing a register per operand;
3. a displaced value waits in the first free register outside the run, or is
   evicted, reloaded from its stack home after the op;
4. its inputs are at `SKIP + i`.

An inline guard is a use of its slot: it keeps the slot where it is, or takes
the first free register. A flush point empties the window. The pass starts from
the entry window of the trace's allocated successor, if any, and adds each
side exit's `live_out` as a use that may stay in the stack home (it takes a
register only if one is free), as the thesis does for values that may be on the
stack.

**What is kept.** Per window op its `SKIP`, and per block the window at its
start, which every edge entering it other than from its predecessor in the
trace is resolved into. Code generation stays forward, as now: each op runs at
its `SKIP`, dirty values are stored when dropped, at flush points and at exits,
and each edge between traces is resolved by the existing transfer (stores, then
a parallel move by windmill peeling). The transfer is emitted at the edge's own
jump, so the critical edges LBBV creates need no splitting (see Trace
building policies).

## Trace building policies

The allocation is correct for any partition into traces, so the policy is
selectable (a feature, or a switch on the JIT context), letting the same
benchmarks and window dumps run under each. In particular, single-block traces
against a frequency-driven policy measures whether traces longer than a block
improve the code.

The thesis's CFGs have no critical edges; LBBV's do, because a jump or select
target is looked up by bytecode position and context, so branches rejoin a
shared version (in life, two blocks each select between the same two blocks).
Without critical edges, every edge between two blocks of a trace joins
consecutive blocks, or is a back edge ending the trace. With them, a trace can
also have a forward edge skipping blocks (from `T[i]` to a join `T[j]`, `j > i +
1`), a back edge leaving from its middle (a latch whose select exits the loop,
with the exit appended after it), or a block jumping to itself.

None of these need the policy to avoid them. The backward pass only relies on
the definition: along each edge between consecutive blocks of a trace, the
window wanted at the start of `T[i + 1]` is the one at the end of `T[i]`. Every
other edge entering a block, from the same trace or another, is resolved at its
own jump by a transfer into the window recorded at the target's start, as
entries into the middle of a trace are in the thesis; a select emits a jump per
target, so no edge needs splitting. A window is recorded at the start of every
block of a trace. The only rule policies keep is the definition's: a trace is
never extended across a retreating edge of the region's depth-first walk, so
the edges between its consecutive blocks all go forward, reducible or not.

- **Single-block.** Every block is its own trace: local allocation, with every
  edge between blocks resolved. Traces are allocated in the region's
  depth-first postorder, so a block starts from the entry window of a
  successor allocated already (every one but a loop's closing edge's target).
- **Unidirectional** (the thesis's choice). Start a trace at a block whose
  predecessors in the region are all in traces already (at first, the
  region's entry), preferring the most frequent, and append the most frequent
  successor not yet in a trace until there is none. Traces are allocated in the
  order found. The thesis proves there is always such a block to start from
  only for CFGs without critical edges; when there is none, start from the most
  frequent block not yet in a trace.
- **Bidirectional.** Start a trace at the most frequent block not yet in one,
  grow it upwards through its most frequent predecessor not in a trace (never
  across a back edge), then downwards as the unidirectional builder does.
  Traces are allocated in the order found.

The frequency-driven policies need a block's most frequent successor. The
hotness countdown stops at zero, so the blocks of the loop that triggered
compilation all read about zero; among equally hot successors, they prefer the
block's final jump to a guard's failure jump, and a select's first target.

## What it replaces

The region's depth-first postorder and per-block plans, the choice of a
block's live-out from its hottest planned successor, and the rules estimating
a displaced value's cost from how the ops above it use its slot. Within a
trace, what is wanted after a point is exactly what the pass has seen used
further down, so the displacement cost needs no look upward.

## Open questions

- Whether side exits' `live_out` pseudo-uses are worth it, or side traces
  should simply load what they read.
- The frequency order among successors that all read zero hotness, beyond the
  tie-breaks above, for the frequency-driven policies.
