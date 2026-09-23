# Bottom-up window allocation (proposal)

A proposal to replace the streaming forward allocator with LuaJIT-style
bottom-up allocation: collect the compiled region up front, compute register
placements in one backward pass over it, then generate code top-down as today
using those placements. The window model is unchanged (an op runs on a
contiguous run `w[SKIP..SKIP + arity]`, operands in the order the op declares
them; every slot's canonical home is its stack slot), and so are the flush
invariants of `docs/jit-register-cache.md`. Where this departs from that
document's rules is listed at the end.

Why backward: walking a block from its end, every use of a value is seen before
its definition, so live ranges need no analysis. When the pass reaches an op,
it already knows where the rest of the region wants each value, so it can
place the op's outputs where their uses want them. The forward allocator
instead places each output wherever its op lands and fixes it up at the next
use, which spills a value (store, reload) when a later op overwrites it, since
it can't know the value is still wanted.

## The region, collected up front

`jit_compile` first collects the transitive closure of blocks reachable from
the entry over jump and select edges (a guard's failure edge, once its thunk is
forced, is a jump like any other). A block compiled in an earlier region stops
the walk: it is entered with its recorded window, a fixed constraint on edges
into it. The walk is a depth-first search that records:

- the postorder, which the backward pass follows (successors before
  predecessors, except across back edges);
- the layout, reverse postorder with each block's fall-through successor
  visited last, so it lands right after the block and its jump is elided as
  now;
- back edges, an edge to a block still on the search stack: its target is a
  loop header.

## Extended basic blocks

A block is a straight line on its fast path, with side edges hanging off its
guards: a guard's failure edge falls through to the residual after it, which
is either the thunk (it stores the dirty registers and exits) or a jump to the
failure block. Neither constrains allocation: a thunk takes whatever window it
finds, and a failure jump reconciles that window with its target's by parallel
moves, off the fast path. So the backward pass treats every block as a straight
line, and side edges only get reconciliation moves in the forward pass. A guard
reads its slot wherever it is (a window register, or the stack home) and adds
no wants.

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
- **Guard, thunk, jump.** Transparent: `W` is unchanged.

A block's end starts from its **live-out**: the wanted window of its
fall-through successor's entry. Its other successors (the other targets of a
select, failure jumps) are reconciled by parallel moves on their edges. A
successor not yet processed, the target of a back edge, has no known entry yet:
its live-out is empty. A block compiled in an earlier region wants its
recorded window.

A block's `W` at its start is its **used-in**: the values it and its
successors want in registers on entry, recorded as its entry window. The pass
records, per window op, its `SKIP` and the `W` before it; per block, its
used-in. That is a few bytes per window op and a register map per block. It
visits each residual once, trying at most `WINDOW` placements per window op.

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
are wanted. That includes the fall-through edge, since its target's used-in is
where the block's live-out came from.

The entry stub loads the entry block's used-in from the stack, since the
interpreter enters from memory.

## Loop headers

With LBBV, a loop's first iteration is peeled while the specialization context
reaches its fixpoint, so the steady-state loop header is its own block. Its
predecessors are the peeled iteration (a forward edge) and the latch (the back
edge).

**Baseline.** The latch is processed before the header, so its back edge sees an
empty live-out: it places its values freely, and its jump to the header
reconciles with the header's used-in by parallel moves each iteration. The
header's used-in comes from the loop body, not from what the peeled iteration
left, and the peeled iteration's live-out is that used-in. So values live
through the loop, such as its invariants and the loop variables, arrive from
the peeled iteration where the body wants them. As I remember LuaJIT's
assembler, it gets the same bias by assembling the loop body first and the
pre-roll after, with a shuffle of the loop-carried values at the loop's end.
That is worth checking against its source before relying on it.

**Using the back edges.** A second backward pass over just the loop's blocks,
with the header's used-in as the latch's live-out, would compute the
loop-carried values straight into the registers the header wants, making the
back edge's reconciliation empty. That costs one more pass over each loop's
blocks; the marked back edges say which blocks those are. The choice between
this and the baseline is open.

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
  is fresh. Every block enters with its used-in, including the region's entry
  (loaded by the entry stub) and a loop header.
- **Rule 2** reverses direction. The successor doesn't adopt the predecessor's
  out-set; the predecessor delivers the successor's used-in. The fall-through
  edge carries only the moves that follow the block's last op, which are none
  when that op's outputs could land where the successor wants them.
- **Rules 3 and 5, and the flush invariants,** are unchanged. Other edges
  reconcile by parallel moves, and the entry stub loads a block's entry window
  from the stack.

## Open questions

- A select's successors: which one is the fall-through whose used-in becomes
  the live-out (the loop continuation, for a for-loop's select)?
- Whether a failure jump's target should contribute wants too, making failure
  paths cheaper at the fast path's expense.
- The loop-header choice above.
