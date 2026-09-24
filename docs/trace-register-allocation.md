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
  any register is a free operand, doesn't hold for the window (see Allocating a
  trace).
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
retreating edge of its depth-first walk dominates the edge's source, and if one
doesn't, it treats every slot the region reads (or that a block outside it
wants in a register) as live into every block of the region. Fixing up only
the cycle's blocks would be unsound: blocks the pass visited before the fix
computed their sets from the cycle's.

**Allocating a trace.** The window is positional: an op at `SKIP` s with arity
k reads `w[s..s+k]` in declared order and writes its output directly above its
inputs, so where an op runs decides which registers it touches, and a value is
useful in a register only if it is where the op reading it needs it. A load
straight into that position costs one instruction, as a move does, so keeping
a value in a register saves something only if it is in place at its next use,
and costs a move every time an op's run lands on it in between. Allocation is
then mostly choosing each op's `SKIP` so values produced and read nearby line
up, and choosing which values stay in registers between their uses at all.

It is destination-driven (Dybvig, Hieb and Butler, "Destination-driven code
generation", 1990): one backward pass over the trace, as one straight line (its
blocks in order, their exits as points on it), where each use of a value says
where it wants the value, and the code above it (its producer, or an earlier
use) satisfies that if it can. The pass keeps **requests**, one per pending use:

- **At(r).** The use reads the slot in register `r`: an operand of an op placed
  already, at `SKIP + i`. Kept, the value is in `r` from its source to the use,
  and `r` is reserved for it in between.
- **Any.** The use wants the value in some register, moved into place at the
  use: one move, from wherever it is.
- **Home.** Dropped: the use loads it from its stack home, one load (and a store,
  if the value was written in the trace since the last flush, as the dropped
  register held its only up-to-date copy).

A request's **source** is the point above its use where the value is known to
be in a register: the op that writes it (its output register), an earlier op
that reads it (that op's input register, which it leaves unchanged), or the top
of the trace. A request never outlives its source: above a write of its slot,
the slot names another value.

At a window op, walking backwards:

1. **Its `SKIP`.** Each usable `SKIP` is costed against the pending requests:
   - an At(r) of another slot in its run, which the op overwrites: the request
     is **demoted** to Any, never moved aside and back (a pending request inside
     the run which the op reads in place, or writes there, is kept): cost 1, or 2
     if the value is dirty;
   - an At(r) of its output outside the run: a move after the op, cost 1;
   - an Any of its output: kept in the output's register if that register is
     free until the use (cost 1, the move at the use), else dropped (cost 2: the
     store the dirty value then needs, and the load);
   - an At(r) of an input in another register: a copy, cost 1.

   The cheapest `SKIP` wins, ties to the one demoting requests whose next uses
   are furthest (Belady), then to the highest `SKIP`: a use placed high leaves
   its definers room below it, where their outputs land on its inputs. An input
   already wanted in place by a later use costs nothing, so a repeated op shape
   settles at the same `SKIP` in every instance, and a value both use (a loop
   invariant, a table the same row is read from) stays put between them.
2. **Its outputs are sources.** Each pending request of an output slot ends
   here: an At(r) is kept (moved into `r` after the op, if the output lands
   elsewhere); an Any is kept in the output's register if it is free until the
   use, else becomes Home.
3. **Its inputs are sources** of every other pending request of their slot: an
   At(r) is kept (copied into `r` if the input is elsewhere); an Any is kept in
   the input's register if it is free until the use, else becomes Home.
4. **Its inputs make new requests**, At(`SKIP + i`), for the code above.

**Any values.** On a straight line a value kept between its source and its use
is one interval. Whether a register is free across it is known at the source:
every op's run and every kept value between were placed on the way up. Each
register records the earliest point at or below the walk where something
occupies it (a run, or a kept value); since the walk only moves up, the
register is free for an interval from the current point to a use exactly when
that point is at or past the use, and no pending At holds the register. A
register given to an Any value is then occupied from its source.

**Other residuals.** An inline guard makes no request: it tests its slot's
register if the window has one, else loads the slot into a register outside the
window. A thunk needs nothing. A flush point ends every pending request: they
become Home, loaded after it. At the top of the trace, pending At requests are
the head's entry window, and pending Any requests become Home: loading a value
at the top to move it later costs more than loading it at its use.

**Block boundaries and exits.** The pass runs through the trace's blocks without
stopping; a block's entry window is the requests kept across its start. At an
edge leaving the trace (a side exit, a select target, the final jump), the
thesis's pseudo-uses become requests, weighted 0 so they never outweigh the
trace's own:

- to a block with an entry window already, its registers as At requests, where
  no request holds that register;
- to a block with no window yet, the slots live into it as Any requests (kept
  only in registers free until the edge: "may stay in memory").

The trace's own continuation from its last block, into its hottest target with
an entry window, is weighted as the trace's own requests.

**Loops.** A trace containing a loop's header and latch plans its back edge
blind: the latch is planned before the header, whose entry window isn't known
yet. Streaming allocation gets this for free: the header adopts the window the
loop is entered with, typically the end of LBBV's peeled first iteration, which
ran the same code, so the back edge transfers almost nothing. A trace with an
edge back into itself is planned twice: the second pass continues the latch
into the header's entry window from the first. The first pass plays the peeled
iteration's part; a third would barely change the header's window.

**The plan.** The pass decides each request's fate (kept in a register from its
source to its use, or Home) and each op's `SKIP`; the window wanted before each
op, and each block's entry window, is then read off the kept intervals in one
sweep over the trace. Every register a window names holds a value it keeps
until its use; registers it doesn't name are free for the code generator to
reuse. Code generation is unchanged: reconcile to the window, run the op at its
`SKIP`, and transfer at every jump.

**Cost.** Each op looks only at the pending requests (at most one At per
register, and Any requests capped at the window's width, the furthest used
first dropped to Home) and at most `WINDOW` `SKIP`s, so a trace is planned in
time linear in its length; a loop's trace twice. The sweep writes each window
entry once.

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
with the exit appended after it, when the exit is as frequent as the loop), or
a block jumping to itself.

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
  region's entry, or when the entry lies inside a loop, the header of the
  outermost loop around it: the block of that cycle at the lowest bytecode
  position), preferring the most frequent, and append the most frequent
  successor while it is not yet in a trace and not across a back edge. Traces
  are allocated in the order found. The thesis proves there is always such a block to start from
  only for CFGs without critical edges; when there is none, start from the most
  frequent block not yet in a trace.
- **Bidirectional.** Start a trace at the most frequent block not yet in one,
  grow it upwards through its most frequent predecessor (never across a back
  edge) while it is not in a trace, then downwards as the unidirectional
  builder does. Traces are allocated in the order found.

Both compare every neighbour, not only those not yet in a trace, and end the
trace when the most frequent one can't extend it. The thesis's rule, the most
frequent neighbour not yet in a trace, relies on its critical edges being
split: a loop end that also exits reaches the header through a block of its
own, compared with the exit, and the trace ends there when the loop is the more
frequent. Without the split the header, already in a trace, would drop out of
the comparison and the trace would carry on into the exit however cold, with
the loop end's window planned for the exit instead of the loop.

The frequency-driven policies need a block's most frequent neighbour, by the
hotness countdown. It stops at zero, so neighbours that tie have both reached
the compile threshold and are both hot, and which one comes first matters
little: one that can extend the trace, then the lowest block id.

## What it replaces

The region's depth-first postorder and per-block plans, the choice of a
block's live-out from its hottest planned successor, and the per-op placement
that kept every value a later op wanted pinned in that register: under the
window's register pressure, every op's run landed on pinned values, which were
moved aside before it and back after it (two moves, where dropping the value
and loading it at its use is one), and each op's `SKIP` drifted with whatever
the code after it left free.
