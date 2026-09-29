# Window allocation: todo

Issues found reviewing the hot loops of queens, nbody and fannkuch_redux with
`just window-hot` and `just jit-disasm`. Counts are from `window-hot` on nbody
3, fannkuch_redux 20 and queens 200 (release, `window_dump`); "per iteration"
is per iteration of the loop named.

- [x] **A loop header's dirty slots were the trace's, not the loop's.** The
  plan marked dirty every slot of the header's window written since the last
  flush anywhere in the trace, the code before the loop included, and the entry
  window added what the first jump into it compiled had dirty. Now a header's
  entry window has dirty only the slots written after it since the last flush.
  nbody's inner loop no longer stores bix, biz and the loop's limit and step
  every iteration: 12% fewer stores executed in nbody 3, 40M fewer
  instructions in nbody 10 (0.3%), and no change in its cycles; no other
  benchmark's instructions changed.

- [ ] **A loop's latch delivers the first pass's header window, not the one the
  header is compiled with.** The second pass plans the latch to continue into
  the header's window from the first pass and recomputes the header's window,
  and the two differ (docs/trace-register-allocation.md, Loops, "Not yet
  handled"). nbody's inner header is `{w0=[8] w2=[15] w3=[17] w5=[16]}` in the
  first pass and `{w0=[10] w2=[16] w5=[8] w6=[15] w7=[17]}` in the second; the
  latch delivers the index and step in w2 and w3, so every iteration's back
  edge moves them into w6 and w7 and reloads biz, bix and the limit, which the
  body evicted.

- [ ] **Dead values are stored.** A dirty value is stored when its register is
  overwritten, at a transfer into a block that doesn't carry it, and at a
  flush, whether or not anything reads the slot again. nbody's inner loop
  stores `j` `[18]` and the temporaries `bm` `[25]`, `[26]`, `[27]` every
  iteration; fannkuch's copy loop (`q[i] = p[i]`, 4.9M iterations) stores `i`
  `[10]`, which the FORLOOP rewrites, and `p[i]` `[11]`, dead after the store.
  The specializer knows which slots are dead at a jump; a dead dirty value
  should be dropped, not stored.

- [ ] **A loop's entry window keeps what is cheap to keep, not what the loop
  pays for.** nbody's inner loop header keeps bix `[8]` and biz `[10]`, each
  read once per iteration, and the body's first op demotes the accumulators
  bivx `[12]` and bivy `[13]` for it (placed for cost 23 where keeping them
  cost 28), so they are loaded and stored every iteration, and `[8]` and `[10]`
  are evicted later in the body anyway and reloaded at the latch. Placement is
  greedy per op against the pending requests; a request carried around a loop
  should weigh what it saves every iteration: a load for a value read, a load
  and a store for one read and written.

- [ ] **A load costs what a move does, so loop invariants are reloaded.**
  fannkuch's copy loop wants each table directly below the key `i` in its
  window, and with a load priced as a move `p` `[0]` and `q` `[1]` share one
  register: each iteration loads `q` at its guard and `p` again at the back
  edge (2 loads per iteration of a 3-op loop, with 7 of the 9 registers in
  use). Inside a loop, a load should cost more than a move, so a free register
  keeps a loop-invariant value rather than reloading it.

- [ ] **A back edge can leave the loop's window for an empty one.**
  fannkuch's flip loop is peeled: its first pass is planned as one trace, but
  the back edge's context has another version of the header, which was a thunk
  when the loop was compiled and so was compiled later in its own region,
  entered with the thunk's empty window. 1.36M of the loop's 3.3M iterations
  take it: the back edge stores `j` `[10]` and `i` `[9]`, the other version
  reloads `p`, `q`, `j` and `i`, runs its guard and jumps into the first
  pass's blocks. A back-edge version should be entered with its loop header's
  window, or planned with the loop.

- [ ] **A slot dirty in two registers is stored twice.** nbody's inner loop has
  `dx` `[20]` dirty in both w6 and w7, and when both are overwritten the
  reconcile stores `[20] <- w7` twice, every iteration. Storing a slot once is
  enough; whether a slot should be cached in two registers at all is worth
  checking too, since the second copy costs a register the loop is short of.
