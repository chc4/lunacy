# Bottom-up window allocation (proposal)

A proposal to replace the streaming forward allocator with LuaJIT-style
bottom-up allocation: collect the compiled region up front, compute register
placements in a backward pass over it, hottest code first, then generate code
top-down as today using those placements. The window model is unchanged (an op
runs on a contiguous run `w[SKIP..SKIP + arity]`, operands in the order the op
declares them; every slot's canonical home is its stack slot), and so are the
flush invariants of `docs/jit-register-cache.md`. Where this departs from that
document's rules is listed at the end.

Why backward: walking a block from its end, every use of a value is seen before
its definition, so live ranges need no analysis. When the pass reaches an op,
it already knows where the rest of the region wants each value, so it can
place the op's outputs where their uses want them. The forward allocator
instead places each output wherever its op lands and fixes it up at the next
use, which spills a value (store, reload) when a later op overwrites it, since
it can't know the value is still wanted.

## The region

`jit_compile` first collects the transitive closure of blocks reachable from
the entry over jump and select edges, including a guard's failure edge once its
thunk is forced into a jump. A block compiled in an earlier region stops the
walk: it is entered with its recorded window, a fixed constraint on edges into
it.

## The processing order

An edge's reconciliation is free when its source is processed after its
target: the source then starts from the target's used-in (below) and computes
the target's reads where they're read. So the processing order decides which
edges cost moves.

The pass processes the region's blocks in the order of a min-heap keyed by
`(hotness, -id)`:

- **Hotness** is the countdown to the compile threshold, so the hottest blocks
  come first and colder ones adapt to them. It stops at zero, so every block
  that has reached the threshold ties.
- **Among ties, the highest block id comes first.** Block ids are allocated
  from a monotonic counter as the specializer reaches new code, so a block's
  successors in straight-line code have higher ids than it. The last block of
  a run is processed first, and each block after the successors created after
  it.

So within a hot loop, whose blocks all tie, the last block, usually the latch,
is processed first, and the rest follow back up the loop. A branch into code
that is still cold is processed after the hot path and adapts to it.

## Extended basic blocks

A block is a straight line on its fast path, with side edges hanging off its
guards: a guard's failure edge falls through to the residual after it, which
is either the thunk (it stores the dirty registers and exits) or a jump to the
failure block. The backward pass treats every block as a straight line:

- a thunk adds no wants, since it takes whatever window it finds;
- a failure jump adds no wants, unless its target is the successor the
  block's live-out (below) comes from: then the live-out applies at the guard
  instead of at the block's end, and the rest of the block after the guard
  carries the reconciliation on its success edge. Otherwise the failure jump
  reconciles by parallel moves.

A guard reads its slot wherever it is (a window register, or the stack home)
and adds no wants.

## The backward pass

The pass carries a **wanted window** `W`: for each register, the slot whose
current value the code after this point expects to find there, or nothing.
Walking a block backwards from its end, each residual turns the `W` after it
into the `W` before it:

- **Window op.** Choose `SKIP` among the usable ones by the moves and loads it
  would force after the op, at the same costs as today (a load or store 4, a
  move 1):
  - an output that `W` wants in a register other than `SKIP + j` costs a move;
  - a wanted value in a register of the op's run that the op doesn't leave
    there (an output of a different slot, or an input of a different slot)
    costs a move, from a free register outside the run where it waits during
    the op, or a load if there is none.

  Ties go to the lowest `SKIP`. The `W` before the op is the `W` after it with
  the op's outputs removed (their old values are dead before the op, unless
  also inputs), its inputs at `SKIP + i`, and each displaced value in the lowest
  free register outside the run, or dropped (reloaded after the op) if there
  is none.
- **Flush point** (any residual other than a window op, inline guard, thunk or
  jump). It clobbers the registers or reads the stack, so nothing survives it
  in a register: `W` before it is empty, and the values `W` wants after it are
  loaded after it.
- **Guard, thunk, jump.** Transparent, except where the live-out applies (see
  Extended basic blocks).

### Used-in and live-out

Two per-block sets connect the blocks, each with one job:

- **used-in(B)**: the slots B itself reads before writing them, each with the
  register B's backward pass placed it in at B's start. It is B's own
  requirement, not its successors': a slot only a later block reads is not in
  it. It is B's entry window, what every edge into B must deliver.
- **live-out(B)**: the used-in of whichever of B's successors was processed
  first, the hottest one by the processing order. It starts B's backward pass,
  so B's definitions of those slots are placed where that successor reads them.
  It is empty when no successor was processed before B, as for a loop's latch,
  whose successor is the loop's first block.

Both are known when B is processed: live-out from successors already
processed, and used-in from B's own pass, as `W` at B's start restricted to
the slots B reads. A slot in `W` at B's end that B neither
reads nor writes is not carried into B's used-in. The pass keeps it in its
register while no op of B needs that register, and otherwise drops it. The
forward pass then loads it wherever `W` first wants it again, at the latest
before B's jump.

A block's other successors reconcile by parallel moves on their edges. An edge
into a block compiled in an earlier region delivers that block's recorded entry
window, which acts as its used-in.

The pass records, per window op, its `SKIP` and the `W` before it; per block,
its used-in. That is a few bytes per window op and a register map per block.
It visits each residual once, trying at most `WINDOW` placements per window op,
and each block goes through the heap once.

Code layout is unchanged: each block's fall-through successor right after it,
its jump elided.

## The forward pass

Code generation stays top-down, as now: the cache it tracks is what the
registers actually hold, and dirty values are handled exactly as today (stored
when a transfer drops them, at flush points, and by a thunk before it exits).
At each window op it reconciles the cache with the recorded `W` before the op
(stores of dropped dirty values, then one parallel move of register moves and
loads), then runs the op at its recorded `SKIP`. A jump reconciles the cache
with its target's used-in. The moves an op's placement costs after it happen at
the next reconciliation, the next op's or the block's final jump. Otherwise
the reconciliations are empty where the backward pass placed values where they
are wanted. That includes the edge to the successor the block's live-out came
from, since that is its used-in.

The entry stub loads the entry block's used-in from the stack, since the
interpreter enters from memory.

## Loops

A loop's blocks are equally hot, so the processing order takes them from the
highest id down: the latch first, before the loop's first block, its
successor across the back edge. The back edge is then the one edge of the loop
processed before its target, and its reconciliation runs every iteration. For
a loop whose blocks all run on every iteration, it costs the same on whichever
of the loop's edges it lands. (With LBBV the loop's first iteration is peeled
while the specialization context reaches its fixpoint, so the steady-state
loop is entered from the peeled iteration by an ordinary edge, processed after
the loop.)

Placements around a cycle depend on each other, so some reconciliation on it
is unavoidable in general. What is open is how much the back edge costs:

- **Nothing wanted at the latch's end.** Its live-out is empty. The values it
  leaves for the loop's first block (the loop-carried ones, such as the loop
  variables) are placed without regard to where they're read next, and the back
  edge moves them there. That is a move each while they stay in
  registers. One the pass dropped, because it wasn't wanted and a later op
  needed its register, costs a store and a load.
- **A second pass over the loop.** Once the loop's blocks are processed,
  process them again, with the loop's first block's used-in as the latch's
  live-out. The loop-carried values are then computed where they're read next.
  The second pass can change the first block's used-in itself, since its
  successors' used-in changed, and the back edge then reconciles with the new
  one. That means fewer moves, and none only when it doesn't change. The cost
  is one more pass over each loop's blocks.

As I remember LuaJIT's assembler, it puts this reconciliation on the same edge.
It assembles the loop body backwards from the loop's end and emits a shuffle of
the loop-carried values (its PHIs) there, with register hints so that a value's
definition tends to land where the loop's start reads it. That is worth
checking against its source.

## Worked by hand

The squares in nbody's `dist2 = dx*dx + dy*dy + dz*dz` (slots dx 20, dy 21,
dist2 23, temporary 24), the ops `NumericIntInt(20, 20, out 23)`,
`NumericIntInt(21, 21, out 24)`, `NumericIntInt(23, 24, out 23)`.

The forward allocator (from `just window-dump nbody`) emits 3 loads, 1 store
and 3 moves:

```
w3 <- [20]; w4 <- w3;                  op at w3   (w5 = dist2, dirty)
[23] <- w5; w5 <- [21]; w6 <- w5;      op at w5   (spills dist2)
w3 <- [23]; w4 <- w7;                  op at w3   (reloads it)
```

Backward, with nothing wanted after the last op:

- `(23, 24, out 23)`: `SKIP` 0, so it wants 23 in w0 and 24 in w1.
- `(21, 21, out 24)`: its output lands at `SKIP + 2`, never at w1, so it costs
  a move at any `SKIP`. `SKIP` 0 would also displace 23 from w0, and `SKIP` 1
  doesn't, so it takes `SKIP` 1: it wants 21 in w1 and w2, keeps 23 in w0, and
  moves its output from w3 to w1 after it.
- `(20, 20, out 23)`: its output can't reach w0 either (a move at any `SKIP`),
  and 21 is loaded after it wherever it runs, so it takes the lowest, `SKIP` 0,
  moving its output to w0 and loading 21 into w1 and w2 after it.

Forward, that is 2 loads, no stores and 4 moves:

```
w0 <- [20]; w1 <- w0;                  op at w0   (w2 = dist2)
w0 <- w2; w1 <- [21]; w2 <- w1;        op at w1   (w3 = dy*dy)
w1 <- w3;                              op at w0
```

Placing dist2 knowing that the next op keeps it saves the spill's store and
reload. The lowest-`SKIP` tie-break still costs moves a lookahead would avoid.
This proposal doesn't add lookahead.

## Departures from `docs/jit-register-cache.md`

- **Rules 1 and 4:** a block no longer enters with an empty window because it
  is fresh. Every block enters with its used-in (the slots it reads, where it
  reads them), including the region's entry (loaded by the entry stub) and a
  loop header.
- **Rule 2** reverses direction. The successor doesn't adopt the predecessor's
  out-set; the predecessor delivers the successor's used-in. The edge to the
  successor its live-out came from carries only the moves that follow the
  block's last op,
  which are none when that op's outputs could land where the successor wants
  them.
- **Rules 3 and 5, and the flush invariants,** are unchanged. Other edges
  reconcile by parallel moves, and the entry stub loads a block's entry window
  from the stack.

## Open questions

- Nested hot loops tie too. An inner loop's latch has two successors: the
  loop's first block across the back edge (a lower id, not processed yet) and
  the inner loop's exit into the outer loop (created later, so a higher id,
  processed first). The latch then takes its live-out from the exit, run once
  per outer iteration, instead of from nothing, and a failure jump's target,
  created when the guard first failed, likewise wins over the block's
  continuation. Telling these apart needs hotness that doesn't stop at the
  threshold.
- Which back-edge treatment above, or something else.
