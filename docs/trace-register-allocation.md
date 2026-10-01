# Trace register allocation for the window (proposal)

A proposal to base the window allocator on trace register allocation (Josef
Eisl, *Trace Register Allocation*, JKU Linz 2018; built for Graal): its trace
building, global liveness and resolution between traces, with allocation
within a trace destination-driven, as the window's positional operands need,
in place of the thesis's register-to-variable allocators.

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
  traces that branch off it; a trace head's `live_in` is a pseudo-definition
  of the values entering it, placed at the top of the head (under SSA that is
  sound: a value that couldn't be defined there would have a definition in the
  head, so it isn't live in). It is one backward pass over the blocks in
  reverse postorder, plus, for each loop, adding what is live into its header
  to every block of the loop (Wimmer and Franz 2010). No fixpoint: in SSA form
  a value live at a loop header can't be killed inside the loop.
- **No lifetime holes**, a separate property: a trace is a straight line, so a
  variable's live range within it is one interval, and one linear pass over
  the trace allocates it.
- **Allocation, one trace at a time**, in the policy's order, most important
  first. The thesis's bottom-up
  strategy is one backward pass over a trace with a map from registers to
  variables and from variables to locations: per instruction, its outputs first
  (their registers become free), then its inputs (where they already are, else
  a free register, else the first register the instruction doesn't use,
  evicted, with a reload after the instruction). It starts from the entry
  locations of an already allocated successor. It deliberately doesn't try
  harder (furthest-first eviction, delayed spill stores, round-robin registers
  were all tried and dropped for compile time). Its premise, that a value in
  any register is a free operand, holds for the window up to a move into the
  op's position, which is cheap (see Moves are cheap).
- **Resolution.** Each trace records where its boundary values are; every edge
  between traces gets the parallel moves between the two, and a loop's back
  edge, which is always the end of a trace, is resolved the same way.

## Mapped onto the window

**Blocks and exits.** An LBBV block is already an extended basic block: a
straight line whose guards branch off it. A guard's failure edge is either its
thunk, an exit to the interpreter, or, once the thunk is forced, a jump to
another block, an edge between traces. A select's targets are edges too. Which
of these edges join blocks of one trace is up to the building policy.

**Liveness of slots.** Variables are stack slots, not SSA values: a slot can be
redefined inside a loop. The single pass with loop-header propagation then
over-approximates, marking a slot live across a loop that redefines it. That is
safe here: every slot has its stack home, so a slot wrongly thought live costs
only register pressure, never correctness. A Lua frame has at most 250 slots,
so a live set is a 256-bit set per block.

The loop step assumes a reducible region, where a loop's header dominates its
blocks. Lua 5.1 bytecode has no `goto`, so its control flow is reducible, but
block versioning isn't bound by that: if two paths reach a loop in different
contexts and join the steady-state loop's versions at different blocks, that
loop has two entries. Liveness has to stay sound for such regions.

**The window is positional.** An op at `SKIP` s with arity k reads
`w[s..s+k]` in declared order and writes its output directly above its inputs,
so where an op runs decides which registers it touches, and a value serves an
op only in the register the op reads it from.

**Moves are cheap.** A move between registers is close to free: register
renaming executes it in the pipeline. What the allocator minimizes is the
loads and stores on hot paths, so keeping a value in a register and moving it
into place beats dropping it and loading it at its use.

**Cost.** Planning a trace is linear, or close to it, in the trace's length;
no part of the approach may be quadratic.

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
1`), a back edge leaving from its middle, or a block jumping to itself.

None of these need the policy to avoid them, or any edge to be split: every
edge other than between consecutive blocks of a trace is resolved at its own
jump, as entries into the middle of a trace are in the thesis, and a select
emits a jump per target. A trace is never extended across a retreating edge of
the region's depth-first walk, so the edges between its consecutive blocks all
go forward, reducible or not.

- **Single-block.** Every block is its own trace: local allocation, with every
  edge between blocks resolved.
- **Unidirectional** (the thesis's choice). Start a trace at a block whose
  predecessors in the region are all in traces already, preferring the most
  frequent, and append the most frequent successor while it is not yet in a
  trace and not across a back edge. The thesis proves there is always such a
  block to start from only for CFGs without critical edges.
- **Bidirectional.** Start a trace at the most frequent block not yet in one,
  grow it upwards through its most frequent predecessor (never across a back
  edge), then downwards as the unidirectional builder does.
