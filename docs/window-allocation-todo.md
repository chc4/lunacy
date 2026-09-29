# Window allocation: todo

Issues found reviewing the hot loops of queens, nbody and fannkuch_redux with
`just window-hot` and `just jit-disasm`. Counts are from `window-hot` on nbody
3, fannkuch_redux 20 and queens 200 (release, `window_dump`); "per iteration"
is per iteration of the loop named.

- [ ] **A loop header's dirty slots are the preheader's, not the loop's.**
  Note [Window allocation] says a loop header's entry window has dirty the
  slots the loop writes, which its back edge brings dirty. Its dirty slots come
  from the first jump to it that is compiled instead, the preheader's, so a
  slot the loop never writes stays dirty for the whole loop and every eviction
  of it in the body stores a value that hasn't changed.
  nbody's inner loop stores bix `[8]`, biz `[10]`, and the loop's limit and
  step `[16]`, `[17]` every iteration (1.8M times each), and its latch loads
  them back. The preheader should store what the loop doesn't write once, and
  the header's window hold it clean.

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
