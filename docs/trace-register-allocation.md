# Trace register allocation for the window (proposal)

A proposal to base the window allocator on trace register allocation (Josef
Eisl, *Trace Register Allocation*, JKU Linz 2018; built for Graal), replacing
the per-block backward planning, whose rules for what a displaced value costs
and what a block's entry window holds have no model behind them.

## The model

- **Traces.** The control-flow graph is partitioned into traces: sequences of
  blocks where each block's successor in the trace is one of its CFG
  successors, and no edge inside a trace is a back edge. Every block is in
  exactly one trace. The unidirectional builder starts a trace at a block whose
  predecessors are all in traces already (at first, the entry), preferring the
  most frequent, and appends the most frequent successor not yet in a trace
  until there is none. Every other edge out of a trace's blocks is an edge
  between traces, into another trace's head or middle.
- **Global liveness**, computed once: `live_in` and `live_out` per block. A
  block's `live_out` is a pseudo-use at its end, keeping values alive for the
  traces that branch off it; a trace head's `live_in` is a pseudo-definition.
  It is one backward pass over the blocks in reverse postorder, plus, for each
  loop, adding what is live into its header to every block of the loop
  (Wimmer and Franz 2010). No fixpoint: in SSA form a value live at a loop
  header can't be killed inside the loop. Inside a trace, liveness has no
  holes, since a trace is a straight line.
- **Allocation, one trace at a time**, most important first. The bottom-up
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
select's targets are edges too. A trace follows each block's most frequent
successor, so a chain of small blocks joined by jumps, like life's
neighbour-count loop, is one trace allocated in one backward pass, where the
per-block planning had a reconciliation at every jump.

**Frequency.** The builder needs to pick a block's most frequent successor.
The hotness countdown stops at zero, so the blocks of the loop that triggered
compilation all read about zero. Among equally hot successors, prefer the
block's final jump to a guard's failure jump, and a select's first target.

**Liveness of slots.** Variables are stack slots, not SSA values: a slot can be
redefined inside a loop. The single pass with loop-header propagation then
over-approximates, marking a slot live across a loop that redefines it. That is
safe here: every slot has its stack home, so a slot wrongly thought live costs
only register pressure, never correctness. A Lua frame has at most 250 slots,
so a live set is a 256-bit set per block. Exits to the interpreter and flush
points need nothing in registers; since the interpreter may read any slot
after an exit, liveness never removes a store of a dirty value, only decides
which values are worth a register.

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

**What is kept.** Per window op its `SKIP`; per block that an edge between
traces enters (trace heads, and blocks entered in the middle of their trace),
the window at its start. Code generation stays forward, as now: each op runs at
its `SKIP`, dirty values are stored when dropped, at flush points and at exits,
and each edge between traces is resolved by the existing transfer (stores, then
a parallel move by windmill peeling). The transfer is emitted at the edge's own
jump, so critical edges, which the thesis excludes, need no splitting.

**Order.** Traces are allocated in the order the builder finds them, the one
from the region's entry first, so a colder trace starts from the entry window
of the hotter trace it jumps into.

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
  tie-breaks above.
