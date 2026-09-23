# JIT register cache (NuN-boxed value caching in GPRs)

Design + implementation plan for caching stack-slot values in registers while
JITting, now that values are 8-byte NuN-boxed `LBoxed` (fit in one GPR).

Branch goal: a **dumb** register allocator that keeps `LBoxed` stack-slot values
in GPRs across JIT code instead of round-tripping every operand through
`state.vals`, plus (later) copy&patch codegen for hot ops.

---

## 1. How lunacy's LBBV + JIT works today (the parts that matter here)

- **Residuals are backend-neutral IR.** Bytecode ops are Rust coroutines
  (`emit_*`) that yield `YieldOp`s, which the specializer drives into a
  `Vec<Residual>` per `Block`. The same residuals feed **both** tiers: the
  specializer's interpreter loop and the native codegen.
- **`Residual::Exec(ResidualExec)`** carries an opaque closure body over
  `(&mut Owner, &mut RunState)`. The interpreter calls it; the JIT emits a
  **static call** to the closure's body.
- **Everything reads/writes `state.vals[state.base + slot]` (memory).** The JIT
  pins `r12=owner, r13=state, r14=&vals[base]`. Guards do inline NuN-box tag
  tests against a slot's stack home, but `Exec` bodies still load/compute/store
  operands through the stack, plus a `call` per op. **That memory traffic + the
  call are what the register cache removes.**
- **JIT ABI:** `JitExec` is `extern "rust-preserve-none"` — no callee-saved
  regs, which is a good fit for a value cache and for copy&patch stencils.
- **`jit_compile` compiles a whole connected region in one buffer.** It emits an
  **entry stub** (prologue + either `jmp extern` to an already-compiled block,
  or fall through into a freshly compiled one), then drains a worklist: blocks
  referenced by `Jump`/`Select` that aren't compiled yet get a label and are
  compiled later in the same call. A `successor` bias makes straightline
  fallthrough elide the jump. Only the top-level entry block gets a JIT entry
  point.
- **Jumps:** if the target is already compiled (including the current region's
  entry, so in-buffer backedges take this path too) → `jmp extern` to it.
  Otherwise a pending label and `jmp =>label`.

### Tier-up and bailout (the crux — I kept getting this wrong)

- **Tier-up:** in the interpreter loop, at a block's first residual its hotness
  counts down from `INITIAL_HOTNESS` (64; 0 with `immediate_jit`). At 0 it
  `jit_compile`s the block (if not already) and calls its JIT entry.
- **Bailout:** JIT code returns a packed `(off, id)`; negative `off` codes are
  bail reasons the interpreter loop handles: `-1` post-trap resume,
  `-2` handle RET, `-3` Select, `-4` resume-at-thunk, `-5` return to interpreter.
  On any bail the interpreter resumes at `(id, off)` **reading from
  `state.vals`** — the interpreter has no registers.
- Therefore: **the interpreter always enters/re-enters a block from memory.** A
  block that is a JIT entry, an `jmp extern` target, or a bail target is entered
  with registers unpopulated — but that is bridged by the **entry stub**, not a
  special "cold prologue."

---

## 2. The register cache model (corrected, final understanding)

Values cached in GPRs are threaded **across blocks** via per-block register
sets, à la tree register allocation (Rong 2009). The canonical home of every
value is always its stack slot (`vals[base+slot]`), so "spilled" == "in its stack
home", which makes reconciliation simple.

Rules — this is the whole allocator:

1. **Fresh block ⇒ empty in-set.** A block that doesn't exist yet has no
   recorded in-set; it is empty. No choice, no phase-ordering, no discovery
   pre-pass. (Earlier I invented a "choose the header in-set to favor the
   backedge / loop-carried-registers" problem — that is **trace-JIT thinking and
   does not apply.** Scrap it.)
2. **Straightline / successor edge ⇒ inherit, no moves.** A block compiled as the
   successor in the same `jit()` call adopts the predecessor's **out-set** as its
   **in-set**. This is the register carry — regs stay live across the edge.
   This is the win.
3. **Jump to an already-existing block ⇒ parallel moves.** Reconcile the current
   out-set to the target's **recorded in-set** (saved per block, e.g. in the
   blocks map / `jit_info`). Covers `jmp extern` to a prior buffer and in-buffer
   backedges. Reconciliation is location-aware (reg↔reg, reg→stack-home,
   stack-home→reg); cyclic reg permutations need a scratch/`xchg` (`preserve-none`
   leaves plenty free).
4. **A freshly-jitted loop header has an empty in-set** (compiled first, no
   in-buffer predecessor), so the backedge into it shuffles-to-empty = flush.
   That is not a lost optimization — it is just what an empty in-set means. The
   cache's win is intra-region straightline carrying, not loop-carried registers.
5. **Entry stub** = the `JitExec`-ABI thing `run` calls. It populates the block's
   recorded in-set **from memory** (`mov reg, [r14 + slot*8]`, same addressing as
   guards) using the same shuffle primitive with source = stack homes, then
   falls through / `jmp`s to the block body. **No-op when the block was compiled
   fresh** (empty in-set). This is why a non-empty in-set on a forward edge is
   safe with interpreter entry: the stub bridges memory→in-set. A block that
   becomes an independent tier-up target later gets its stub lazily via its own
   `jit_compile` (hits the `jmp extern` path).

### Flush points — everything reduces to two invariants (from the original plan)

There are **no extra constraints** beyond these two; every "special site" is an
instance of one of them:

- **Invariant 1:** flush live regs before code that does an **unknown stack
  reference**. A **bailout is exactly this** — the interpreter resumes reading
  the stack, so flush before exiting.
- **Invariant 2:** flush live regs before code that **clobbers registers**.

Consequences (not new rules — just applications):

- **Guard failure is NOT automatically a bailout.** The fail path (off+1) is an
  ordinary edge to another block, reconciled by rules 2/3. It is only a bailout
  when off+1 is a `Thunk`, and a `Thunk` is handled **identically to any other
  flush point** (flush, exit).
- **GC is an explicit `Residual::GC`**, already visible to the JIT. It is a
  flush point (invariant 2 / it's a call): flush cached regs — **including cell
  pointers** — to the stack before it, and the collector traces them off the
  stack as normal. **No stackmap, no extra GC root scanning.**
- Clobbering calls (`NativeCall`, `LuaCall`, closure-body `Exec` calls) and
  anything that can reallocate/move `vals` are invariant-2 flush points.

---

## 3. Making dataflow visible + copy&patch

The allocator needs to know which slots each op reads/writes; today `Exec` is an
opaque closure so the JIT can't see its dataflow:

- **`Residual::ExecWindow(op)`**, roughly
  `|[[_; SLOTS], a] -> [[_; SLOTS], a] { become _r([a+1]) }`: the op names its
  operands directly by their stack slots, and the stack window plus
  register-carried values flow between stencils by tail call. Interpreter mode:
  retrieve stack slots, call, flush stack slots. JIT mode: the register
  allocator reconciles the op's operands with the current window (the live
  `slot→register` map) at the op, deferring flushing as long as we only see
  more `ExecWindow` ops.

**Copy&patch (the part worth the machinery).** Instead of emitting a `call` to
the `Exec` closure body, splat the op's compiled **template/stencil** into the
JIT buffer and slice off the trailing `become` tail call (copy&patch; cf.
patchouly, <https://github.com/gudzpoz/patchouly>). Why it's the right fit here:
it keeps lunacy's "one implementation per op" property (the stencil *is* the
compiled closure body — no duplicated op semantics in the JIT) while inlining
with register operands and no call. Costs to go in eyes-open: LLVM doesn't pin
stencil register usage/layout, so operands must be expressed as **relocations**
(extern-symbol holes) to patch, not "byte N"; reserve a fixed register partition
(pinned `owner`/`state`/`base` vs. value-cache regs); `become` /
`explicit_tail_calls` is nightly.

---

## 4. Implementation plan (ordering)

1. **Expose dataflow.** Give the JIT visibility into each exec's read/write slots
   — the `ExecWindow` residuals above, naming their operands' stack slots. No
   behavior change; interpreter keeps calling the body.
2. **JIT-local `slot→Gpr` cache** in `jit_block`: linear-scan allocation,
   oldest-eviction (evict→flush to stack home). Implement the per-block in-set /
   out-set recording + the reconciliation primitive (rules 1-5). Still call the
   closure bodies for now (store operands back just-in-time around calls). Flush
   at flush points (thunks/bailouts, `Residual::GC`, clobbering calls, unknown
   stack refs). Validate hard under `gc_stress`.
3. **Entry stub populates recorded in-set from memory** (rule 5); no-op for fresh
   blocks. Persist each block's recorded in-set (blocks map / `jit_info`).
4. **Copy&patch** for the hot ops only (numeric `NumericIntInt` &c.,
   `gettable_href`): build stencils, patch operand relocations, drop the `become`
   tail.

### Verification
- `nix develop` then `just run nbody` (see repo memory `nix-devshell`).
- Correctness gate: run under `gc_stress` to catch any cell pointer that's live
  in a reg but not flushed at a GC/clobber point.
- Perf: `perf` feature emits `/tmp/perf-<pid>.map`; compare nbody / life against
  the interpreter and current JIT.
