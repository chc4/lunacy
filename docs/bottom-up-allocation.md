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

Every block needs an **entry count**, how often the interpreter has entered
it. The hotness counter doesn't serve: it counts down to the compile threshold
and stops at zero, so by the time a region is compiled every block of its hot
loops, and any block entered as often as the threshold, reads zero. A count that
keeps going (like the `graph` feature's) orders them, and blocks in deeper loop
nests have higher counts.

A block's **preferred successor** is its most-entered one: its final jump's
target, a select's target, or a guard's failure jump, whichever the
interpreter entered most.

## The processing order: chains

An edge's reconciliation is free when its source is processed after its
target: the source then starts from the target's used-in (below) and computes
the target's reads where they're read. So the order decides which edges cost
moves. Processing strictly hottest first isn't enough. A block would be
processed before its colder successors, so its edge into even a slightly
colder successor would cost moves, and in a loop `H → {A (90%), B (10%)} → L →
H` that is the edge `H → A` on 90% of iterations.

Instead the pass processes **chains**. Pop the most-entered unprocessed block
from a max-heap of the region's blocks keyed by entry count, and follow
preferred successors from it until reaching one of:

- a block already processed;
- a block outside the region;
- a block already on the chain, which means the chain went round a loop.

Then process the chain from its end back to its start, so each block is
processed after its preferred successor, and repeat until the heap is empty.
In the example the chain is `H → A → L`, closed by `L → H`, processed `L`, `A`,
`H`. Then `B`, whose preferred successor `L` is processed, forms a chain of its
own. The only edges processed before their targets are a closed chain's
closing edge (`L → H`) and edges to a successor that isn't its source's
preferred one, which is colder by definition (`H → B`). Hot code is placed first
and colder code adapts to it.

Code layout follows the chains, each block's preferred successor right after
it, so the hot path falls through with its jumps elided.

## Extended basic blocks

A block is a straight line on its fast path, with side edges hanging off its
guards: a guard's failure edge falls through to the residual after it, which
is either the thunk (it stores the dirty registers and exits) or a jump to the
failure block. The backward pass treats every block as a straight line:

- a thunk adds no wants, since it takes whatever window it finds;
- a failure jump to a block that isn't the preferred successor adds no wants;
  its edge reconciles by parallel moves, off the hot path;
- a failure jump to the preferred successor is where the block's live-out
  (below) applies, at the guard instead of at the block's end. The rest of the
  block after the guard is then the colder path, and its success edge carries
  the reconciliation.

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
- **live-out(B)**: the used-in of B's preferred successor, when that was
  processed first. It starts B's backward pass, so B's definitions of those
  slots are placed where the successor reads them. It is empty for a chain's
  closing block, whose preferred successor is the chain's own start.

Both are known when B is processed: live-out because the chain order processes
B's preferred successor first, and used-in from B's own pass, as `W` at B's
start restricted to the slots B reads. A slot in `W` at B's end that B neither
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
are wanted. That includes the edge to the preferred successor, since the
block's live-out is its used-in.

The entry stub loads the entry block's used-in from the stack, since the
interpreter enters from memory.

## Loops

A loop's blocks are entered about equally often, so the chain from its hottest
block follows the loop round and closes on itself. The closing block, usually
the latch, is processed first, before its successor at the chain's start. Its
closing edge is the one edge of the loop processed before its target, and its
reconciliation runs every iteration. For a loop whose blocks all run on every
iteration, it costs the same on whichever of the loop's edges it lands.
(With LBBV the loop's first iteration is peeled while the specialization
context reaches its fixpoint, so the steady-state loop is entered from the
peeled iteration by an ordinary edge, processed after the loop.)

Placements around a cycle depend on each other, so some reconciliation on it
is unavoidable in general. What is open is how much the closing edge costs:

- **Nothing wanted at the closing block's end.** Its live-out is empty. The
  values it leaves for the chain's start (the loop-carried ones, such as the
  loop variables) are placed without regard to where they're read next, and the
  closing edge moves them there. That is a move each while they stay in
  registers. One the pass dropped, because it wasn't wanted and a later op
  needed its register, costs a store and a load.
- **A second pass over the chain.** Once the chain is processed, process it
  again, with the chain start's used-in as the closing block's live-out. The
  loop-carried values are then computed where they're read next. The second
  pass can change the chain start's used-in itself, since its successors'
  used-in changed, and the closing edge then reconciles with the new one. That
  means fewer moves, and none only when it doesn't change. The cost is one more
  pass over each closed chain.

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
  preferred successor carries only the moves that follow the block's last op,
  which are none when that op's outputs could land where the successor wants
  them.
- **Rules 3 and 5, and the flush invariants,** are unchanged. Other edges
  reconcile by parallel moves, and the entry stub loads a block's entry window
  from the stack.

## Open questions

- Where the entry counts come from: a count kept alongside the hotness
  countdown, or the countdown replaced by a count compared against the
  threshold.
- Which closing-edge treatment above, or something else.
