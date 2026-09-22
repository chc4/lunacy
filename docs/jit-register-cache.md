# JIT register cache (NuN-boxed value caching in GPRs)

Design + implementation plan for caching stack-slot values in registers while
JITting, now that values are 8-byte NuN-boxed `LBoxed` (fit in one GPR).

Branch goal: a **dumb** register allocator that keeps `LBoxed` stack-slot values
in GPRs across JIT code instead of round-tripping every operand through
`state.vals`, plus (later) copy&patch codegen for hot ops.

---

## 1. How lunacy's LBBV + JIT works today (the parts that matter here)

- **Residuals are backend-neutral IR.** Bytecode ops are Rust coroutines
  (`emit_*` in `generator.rs`) that yield `YieldOp`s. `Specializer::compile_one`
  (`generator.rs:1605`) drives them into a `Vec<Residual>` per `Block`. The same
  `Vec<Residual>` feeds **both** tiers:
  - the interpreter loop `Specializer::run` (`generator.rs:1908`)
  - the native codegen `Specializer::jit_block` (`jit.rs:352`)
- **`Residual::Exec(ResidualExec)`** carries an opaque
  `body: Rc<dyn Fn(&mut Owner, &mut RunState)>` (`generator.rs:150`). Interpreter
  calls it (`(f.body)(owner, &mut state)`, `generator.rs:2058`); the JIT pulls its
  fn-ptr via `get_ptr_from_closure` and emits a **static call** to the body
  (`jit.rs:570`). `ResidualExec` already has an unused
  `template: Option<Rc<dyn Fn()->()>>` field (`generator.rs:153`) reserved for
  copy&patch.
- **Everything reads/writes `state.vals[state.base + slot]` (memory).** The JIT
  pins `r12=owner, r13=state, r14=&vals[base]` (see prologue comment
  `jit.rs:256`). Guards already do inline NuN-box tag tests against
  `r14 => LBoxed[idx]` (`jit.rs:436-514`), but `Exec` bodies still load/compute/
  store operands through the stack, plus a `call` per op. **That memory traffic +
  the call are what the register cache removes.**
- **JIT ABI:** `JitExec` is `extern "rust-preserve-none"` (`jit.rs:45`) — no
  callee-saved regs, which is a good fit for a value cache and for copy&patch
  stencils.
- **`jit_compile` (`jit.rs:250`) compiles a whole connected region in one
  buffer.** It emits an **entry stub** (prologue + either `jmp extern` to an
  already-compiled block, or fall through into a freshly compiled one,
  `jit.rs:259-285`), then drains a worklist: blocks referenced by
  `Jump`/`Select` that aren't compiled yet get a `DynamicLabel` in
  `jctx.pending` and are compiled later in the same call (`jit.rs:293-310`). A
  `successor` bias makes straightline fallthrough elide the jump
  (`jit.rs:687`, the `skip` flag). Only the top-level entry block gets
  `jit_info.entry` set (`jit.rs:347`).
- **`emit_jump` (`jit.rs:362`):** if the target is already in `jctx.blocks`
  (compiled — including the current region's entry, inserted at `jit.rs:280`, so
  in-buffer backedges hit this path too) → `jmp extern target_ptr`. Otherwise a
  pending `DynamicLabel` and `jmp =>label`.

### Tier-up and bailout (the crux — I kept getting this wrong)

- **Tier-up:** in `run` (`generator.rs:1922-1937`), at `off==0` a block's hotness
  counts down from `INITIAL_HOTNESS` (64; 0 with `immediate_jit`). At 0 it
  `jit_compile`s the block (if not already) and calls `jit_info.entry`.
- **Bailout:** `jit_entry` returns a packed `(off, id)`; negative `off` codes are
  bail reasons handled in `run` (`generator.rs:1942-1976`): `-1` post-trap resume,
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
   `jit_compile` (hits the `jmp extern` path, `jit.rs:273`).

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
- **GC is an explicit `Residual::GC`** (`jit.rs:721`), already visible to the JIT.
  It is a flush point (invariant 2 / it's a call): flush cached regs — **including
  cell pointers** — to the stack before it, and `step_published` (`jit.rs:105`)
  traces them off the stack as normal. **No stackmap, no extra GC root scanning.**
- Clobbering calls (`NativeCall`, `LuaCall`, closure-body `Exec` calls) and
  anything that can reallocate/move `vals` are invariant-2 flush points.

---

## 3. Making dataflow visible + copy&patch

The allocator needs to know which slots each op reads/writes; today `Exec` is an
opaque closure so the JIT can't see its dataflow. Two mechanisms from the plan:

- **`Residual::Storage` → `Option<Gpr>` token:** allocate a GPR token for a slot
  via linear scan, evicting the oldest under register pressure (evict = flush to
  stack home). Interpreter mode: retrieve stack slot, use, flush.
- **`Residual::ExecWindow(template, operands)`**, roughly
  `|[[_; SLOTS], a] -> [[_; SLOTS], a] { become _r([a+1]) }` with
  `operands = vec![Gpr(a)]`: the stack window plus register-carried values flow
  between stencils by tail call. Interpreter mode: retrieve stack slot, call,
  flush stack slot. JIT mode: use the live `slot→Gpr` map to defer flushing as
  long as we only see more `Storage`/`ExecWindow` ops.

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
`explicit_tail_calls` is nightly. Reuse the reserved `ResidualExec.template`
field (`generator.rs:153`).

---

## 4. Implementation plan (ordering)

1. **Expose dataflow.** Give the JIT visibility into each exec's read/write slots
   — either the `Storage`/`ExecWindow` residuals above, or a `reads/writes`
   annotation on `ResidualExec`. No behavior change; interpreter keeps calling
   the body.
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
   tail. Reuse `ResidualExec.template`.

### Verification
- `nix develop` then `just run nbody` (see repo memory `nix-devshell`).
- Correctness gate: run under `gc_stress` to catch any cell pointer that's live
  in a reg but not flushed at a GC/clobber point.
- Perf: `perf` feature emits `/tmp/perf-<pid>.map`; compare nbody / life against
  the interpreter and current JIT.

## 5. Status / staging (implementation)

**The value in the window is the whole `LBoxed` (any type), never an unboxed
number.** NuN-boxing is the enabler precisely because *every* Lua value — nil,
bool, number, table, closure, string — is one GPR-sized word, so the register
window/cache pins arbitrary `LBoxed` values, not just numbers. A window op takes
`LBoxed` operands and returns an `LBoxed`, reusing the VM's own `LBoxed` /
`numeric_op` / `box_lvalue` semantics. **Do not reimplement NuN boxing anywhere**
— that was a wrong turn (a duplicated-constants `lunacy-ops` crate) and has been
removed.

Verified environment fact: a fresh git worktree is missing the path-dep
submodules; symlink `dynasm-rs`, `memmap2-rs`, `lua_benchmarking` (and `target`)
from `/workspace` before building (see memory `nix-devshell`). `just test` is the
green gate (default features ⇒ jit on).

**M1 — DONE (interpreter windowing, jit splat disabled).** `ExecWindow` is
**closure-based, exactly like `Exec`** — no op enum, so no processing site
enumerates users. New `WindowExec { name, ins: SmallVec<u16>, out: u16, body,
template }` where `body: Fn(&mut Owner, &mut RunState, &[LBoxed]) -> LBoxed`
receives the values read from `ins` and returns the value written to `out`;
`owner`/`state` remain for ambient needs (heap/intern/constants) but the *windowed
operands* flow as values. `Residual::ExecWindow(WindowExec)` +
`YieldOp::ExecWindow(WindowExec)`. `emit_numeric`'s dynamic value/value arm yields
one whose closure captures the op and reuses the VM's own
`numeric_op`/`box_lvalue` (zero duplication); any other op (move, gettable, …) can
be a window op just by supplying its own closure. `run` executes it generically
(load `ins` slots → call `body` → store `out`); `dump` prints `window(name)`;
`jit_block` bails (interpreter runs the closure). Verified: `just test` fully
green; a hot numeric loop under `immediate_jit` returns the correct result via the
JIT→bail→interpreter path. No new crate.

**M2 — copy&patch splat. Open design point:** a patchouly `#[stencil]` crate is
**extraction-only** — compiled by `build.rs` (`patchouly_build::StencilSetup`)
into an `.rlib` parsed for machine code; it is NOT linked as a normal dependency
(its generated stencils reference an undefined `copy_and_patch_next` that would
fail a normal link) and it cannot depend on `lunacy` (build cycle). So the stencil
body needs `LBoxed`'s real semantics available in a crate that does **not** pull in
`lunacy`. Plan: factor the value layer (`LBoxed` + immediate number/bool/nil ops +
`LValue`/`numeric_op` as needed) into a leaf `lunacy-value` crate depended on by
both `lunacy` and the extraction-only `lunacy-stencils`; the heap-unbox cases stay
in `lunacy` via a local trait if they entangle GC. Then the `#[stencil]` wrappers
`#[inline]` the shared `LBoxed` op, extraction emits the stencils, and `jit_block`
replaces the `ExecWindow` bail with a `PatchBlock` splat. Scope of the split
(how much of the GC-entangled value model must move) is the thing to nail down
before writing it.

**M3+.** Register cache / per-block in-set threading (section 2) — pinning
arbitrary `LBoxed` window values in GPRs across ops.

### Key code references
- `generator.rs:150-166` `ResidualExec` (+ reserved `template`), `:1605`
  `compile_one`, `:1908` `run`, `:1922-1976` tier-up + bail codes, `:2058`
  interpreter `Exec` dispatch, `:999-1014` `Residual` enum.
- `jit.rs:45` `JitExec` ABI, `:250` `jit_compile` (entry stub + worklist),
  `:352` `jit_block`, `:362` `emit_jump`, `:383` `emit_bailout`, `:436-514`
  inline guards via r14, `:570` `Exec` static call, `:592/643` Lua/NativeCall,
  `:691` Ret, `:702` Select, `:721` `Residual::GC`, `:728` Thunk bail.
