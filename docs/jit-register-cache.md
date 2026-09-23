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

### Tier-up and bailout

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

## 2. The register cache model

Values cached in GPRs are threaded **across blocks** via per-block register
sets, à la tree register allocation (Rong 2009). The canonical home of every
value is always its stack slot (`vals[base+slot]`), so "spilled" == "in its stack
home", which makes reconciliation simple.

Rules — this is the whole allocator:

1. **Fresh block ⇒ empty in-set.** A block that doesn't exist yet has no
   recorded in-set; it is empty. No choice, no phase-ordering, no discovery
   pre-pass: choosing a loop header's in-set to carry registers around the
   backedge is a trace-JIT concern and does not apply.
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
opaque closure so the JIT can't see its dataflow. Window ops make it visible
(details in `Note [Register window]`, `src/window.rs`):

- **`YieldOp::Storage(slot, Access)` → `ResumeArg::Storage(Gpr)`:** the emit
  site gets an **opaque token** per operand, minted by the specializer and
  recorded as `Residual::Storage(token, access)`. LBBV does no register
  allocation.
- **`Residual::ExecWindow(Rc<dyn Window>)`**, built from those tokens: inputs are
  read-only and only outputs are written back (`windowed!(.., (a, b) -> (d))`),
  so a register caching a slot only ever holds that slot's value. An op always
  runs on a contiguous run of the window, `w[SKIP..SKIP + arity]`.
- **JIT mode** (`src/window_alloc.rs`, `Note [Window allocation]`): `Storage`
  only records its token; the op, with all of its operands known, is placed at
  the cheapest `SKIP` by resculpting the window from `SKIP` on — inputs moved
  from the register caching them or loaded, displaced values moved to spare
  registers or evicted — with a one-op lookahead. Flushing is deferred to the
  end of the run. Interpreter mode: the op at `SKIP` 0; load the inputs from
  their stack homes, run, flush the outputs (`Storage` is a no-op).

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
`numeric_op` / `box_lvalue` semantics. **Never reimplement NuN boxing**: op
bodies use the VM's own.

Verified environment fact: a fresh git worktree is missing the path-dep
submodules; symlink `dynasm-rs`, `memmap2-rs`, `lua_benchmarking` (and `target`)
from `/workspace` before building (see memory `nix-devshell`). `just test` is the
green gate (default features ⇒ jit on).

**Proven model (`src/bin/windowed.rs`, then ported to `src/window.rs`).**
- The register window is **scalar** `rust-preserve-none` params, never
  `[LBoxed; N]`: Rust passes arrays by pointer whatever the ABI, which puts the
  window in memory. (`unadjusted` isn't available on this toolchain.) Stencil ABI:
  fixed params `owner, state, base` (r12/r13/r14, the JIT's pinned regs) then the
  window `w0..w7` = r15, rdi, rsi, rdx, rcx, r8, r9, r11. preserve-none passes
  12 integer arguments in registers, but the 12th, rax, can't be a window
  register: a `become` compiled as an indirect jump through the GOT has LLVM load
  its target into rax even when rax carries an argument (it is the only register
  eligible for the target outside the arguments), and that load stays in the
  copy — `check_windows` caught it clobbering w8. `owner` is a ZST token that
  can be forged at JIT/interpreter transitions (the JIT helpers already do);
  dropping it as a stencil param would free r12 for a 9th window register.
- `windowed!(Name, [captures], [const params], |owner, state, base| (inputs) -> (outputs) { body })`
  is a **generic**, op-agnostic mechanism used inline at the emit site, exactly
  like `define_exec!` — all of an op's code (static and dynamic) stays in its
  `emit_*`. It generates a struct of **captures** (hole values) + the operands'
  `Gpr` tokens implementing the `Window` trait, an `#[inline(always)]` body
  shared by both tiers, and `__stencil::<SKIP>`, with operand `i` in window
  register `SKIP + i` (`stencil(skip)`). Inputs are bound as values and only
  outputs are written back. `src/window.rs` holds only
  the mechanism (macro, `Window`, tokens, `Capture`, holes, copier); no op
  templates.
- Captures: any `Copy` type of at most 8 bytes (blanket `Capture` impl, raw bits).
  Holes are `extern_weak` statics (`__lunacy_holeN`), read through a const-generic
  index so monomorphization picks the hole; an op with more captures than
  `MAX_HOLES` references `unresolved_window_hole__too_many_captures`, a plain
  (non-weak) never-defined extern, so it fails loudly at link time (verified).
- Under plain PIE a hole read is a RIP-relative load from the hole's GOT slot.
  Holes can't be found by scanning for `0x0` or by operand order, so the copier
  reads this executable's own dynamic relocations (goblin, GLOB_DAT → GOT slot),
  matches each disp32's RIP target, and repoints it at a shared value pool laid
  after the code (the dynasm path will do this with pool labels + `finalize`).
- Each op's stencils end in `become` to the op's **own** private continuation
  (`inline(never)`, and it `black_box`es the window — an empty internal callee
  lets LLVM delete the tail call and every computation feeding the window).
- The copier (`stencil_body`) decodes the stencil with yaxpeax-x86. Well-formed =
  every exit jumps to the continuation (`jmp rel32`, `jmp *[rip+got]`, or
  `jmp *reg` loaded from the GOT slot — rustc uses `-Z plt=no`, and LLVM may
  hoist that load above the epilogue), redirected to the copy's end so the next
  stencil falls through. A final `become` is sliced off; when cold code follows
  it (a panic path, ending in a call that never returns — table ops have
  several), the whole body is copied with a `ud2` after it. Every other RIP-relative reference is reported with its field, the
  end of its instruction (the true RIP base, even with a trailing immediate) and
  its absolute target:
  - `holes` — loads of a hole's GOT slot → repointed at the pool;
  - `nexts` — other references to the continuation (a duplicated tail) → the
    copy's fall-through point (direct), or a pool slot holding it (indirect).
    Handled but not yet observed in practice;
  - `relocations()` — everything else: calls out of line (e.g. `IndexMap`), GOT
    slots, rodata → re-targeted at their original absolute address, in rel32
    range because JIT memory is mapped within ±2GiB of the binary.
  In the JIT all three become dynasm relocations patched at `finalize`;
  `assemble` does the same by hand in a near-mapped buffer.
- Calls are fine anywhere (they return). A jump that leaves the stencil without
  being a `become` would skip the rest of the chain, so the copier rejects it:
  a sibling tail call, or an indirect jump like a jump table (its entries lead
  back into the original function). An opt-level 0 `NumericIntInt` has one
  (unfolded `match OP`); optimized builds don't. The copier (`Image::load`,
  `stencil_body`, `assemble`) returns a `StencilError` rather than panicking, so
  the JIT can leave the op to the interpreter; `check_windows` skips (and
  logs) ops it rejects. Debug builds are otherwise copyable now
  (their un-inlined helper calls and assertion panics are just relocations). The
  interpreter runs any window op regardless.

**M1 — DONE: generic windowed ops in the generator (JIT splat still disabled).**
`Residual::ExecWindow(Rc<dyn Window>)`, like `Exec`'s closure, keeps processing
sites generic; its operands are bound by `Residual::Storage` (section 3). The
interpreter runs `<dyn Window>::interp`: load the inputs from their stack homes,
run the body with captures from the struct, flush the outputs (it can't run the
stencil itself: holes read 0 until patched). The first user is `emit_numeric`'s
dynamic int-int arm: `windowed!(NumericIntInt, [], [OP: Opcode], .. (lhs, rhs) -> (dest))`
inline (body = the VM's own `numeric_op`/`box_lvalue`), operands bound by three
`Storage`s, instance picked with `dispatch_numeric_window!` for all six opcodes;
the constant-operand arms keep their `Exec` closures.

Verification:
- `just test` green, including the window tests in debug: a chain shifting along
  (2, 3, 4, nil) — Add at 0, Mul at 1, AddK at 2 (hole) → Flush, inputs
  unchanged; a stencil calling an out-of-line helper (its call
  appears in `relocations()` and the copy calls it correctly); a branchy stencil
  whose both arms fall through; and two outputs writing one slot is rejected.
- Golden `window_chain.lua`: dependent arithmetic in one block becomes a single
  run of `Storage`/`ExecWindow` residuals (visible in the `graph` feature's
  `func_N.dot`).
- `just test-stencils` (opt-2): the same tests on optimized stencils, then the
  golden suite with feature `check_windows`, which copy&patches **every window
  op the interpreter executes** (the real emit-site ops) and asserts the native
  result matches the interpreter bit for bit. `NumericIntInt` MOD/POW (libm
  calls, relocated) pass it at opt-2.
- Note: the specializer only runs for *calls* to Lua functions; top-level chunk
  code stays in the plain interpreter, so test programs must do their work inside
  a function. An arithmetic program run that way matches reference Lua in the
  debug build, `immediate_jit`, and under `check_windows` (~700k LBBV residuals).
- Pre-existing bug, untouched: `numeric_op` MOD is truncated `%`, not Lua's
  floored modulo (`-3 % 7` gives `-3`).

**M2 — DONE: JIT register allocation + stencil splat.** `src/window_alloc.rs`
allocates each run of window residuals (see `Note [Window allocation]`);
`jit_block` lowers its plan (loads/stores against r14, moves between the window
registers with r10 as scratch) and splats each op's stencil body between
`sub rsp, 8`/`add rsp, 8` (block code keeps rsp 16-aligned; stencils expect the
alignment just after a call). Holes and indirect continuation references become
dynasm relocations to 8-byte pool entries emitted after the region's epilogue;
direct ones a relocation to a label at the copy's end; other RIP-relative
references `value_relocation`s to their absolute target (the buffer's base is
known). Any other residual flushes the window first; residuals inside a run get
no label, so a jump into a run fails to assemble; with `gas`, a run is charged
at its first residual. An op whose stencil the copier rejects at every `SKIP`
flushes and bails to the interpreter, which runs it from the stack.

Hand analysis that shaped the allocator (nbody `advance`, worked for a
4-register window, 3-wide `(lhs, rhs) -> (dest)` ops at `SKIP` 0 or 1, to
study register pressure):
- block 94 (`dz = biz - dz; dist2 = dx*dx + dy*dy + dz*dz`): 5 loads, 3 stores,
  7 moves vs 12 loads/6 stores through the stack (floor 4/3; one spill of `dz`,
  since only one register is spare beside a 3-register op);
- block 100 (`bm`, `bivx/y/z -= d* * bm`): 10 loads, 5 stores vs 16/8 (floor
  9/5); the allocator also finds a 6-move plan against 8 by hand.
Lessons: a result lands at `SKIP+2`, so it is read in place only as the next
op's `rhs` at `SKIP+1` (else one move); `x*x` needs a copy; evicting a dirty
value costs a store only if the slot is written again later in the run
(otherwise it is the run-end store moved earlier); eviction is otherwise by
farthest next read. Both runs are unit tests pinning these counts at width 4
(the allocator takes a width for testing) and at the full 8-register window,
where nothing is evicted and both reach the load/store floor (every slot read
before written loaded once, every written slot stored once): 4 loads/3
stores/5 moves and 9/5/4. Block 94's 5 moves are the minimum by hand: a copy
for each of `dx*dx`, `dy*dy`, `dz*dz`, and each `dist2 += t` needs one, since
putting `t` right after `dist2` means running its producer at `SKIP+1`, whose
span covers `dist2`. Plus an
exhaustive correctness sweep at width 4 executing plans on a symbolic machine.

**Table ops as window ops.** `emit_gettable`'s `gettable_href` is
`GetTableHref: (table) -> (dest)` (captures: the witness index, and the constant
key for the debug check) and `emit_settable`'s `settable_href`, when the value
is in a register, `SetTableHref: (table, value) -> ()` (captures: the witness
index and the value's expected `LType` for the debug check; const param: whether
the store retypes the key and bumps the epoch); a constant value keeps an `Exec`
closure, sharing the store with the window op. Their stencils call into the
table code (23 relocations for a get) and all copy at every `SKIP`. They join
runs, but runs still end at each `href_init` + `select`: a field not yet seen
needs a runtime key lookup and a block split. The multi-op runs of nbody's
`advance` with them, worked by hand for the 8-register window (loads/stores/
moves; loads and stores at the floor):

| run | now | with the table ops as `Exec`s |
|---|---|---|
| `bi.vx, bi.vy, bi.vz = bivx, bivy, bivz` (3 sets) | 4/0/0 | 6 loads |
| `dx = bix - bj.x` | 2/1/0 | 3/2 |
| `dz = biz - bj.z; dist2 = ...` | 4/3/5 | 5/4 |
| `bm = bj.mass * mag; bivx -= dx * bm; ...` | 9/5/4 | 10/6 |
| `bj.vx = bj.vx + dx * bm` | 3/2/2 | 5/3 |
| ... plus `j += step` | 5/3/2 | 7/4 |
| `mag = dt / (mag * dist2)` | 3/2/0 | 3/2 |

In `bj.vx = bj.vx + dx * bm` both moves are forced by the window's shape: the
got value must sit right before the product, whose op covers the register the
get left it in, and `bj` must sit right before the sum. The allocator's tests
pin every row, and the exhaustive sweep covers all three op shapes.

Verification: `just test` (adds the golden suite with `immediate_jit`: in debug
the copier rejects `NumericIntInt`'s jump table, exercising the fallback) and
`just test-stencils` (adds it at opt-2, where window ops run as splatted
stencils under the allocator). Golden `window_nbody.lua` runs `advance` hot.

Open items:
- A copied body with cold code after its `become` keeps the `become` as a
  jump over the cold code (for a GOT-indirect `become`, a load from the pool and
  an indirect jump). Laying the hot path out so the jump becomes a fall-through
  would need the body's blocks reordered.
- A window op's body reaching stack slots other than through its operands is a
  documented rule (Note [Register window]), not a checked one.
- Jump tables in stencils. (Fat-LTO release builds do keep each op's
  continuation a real tail target: `just run nbody` copies all 8
  `NumericIntInt` stencils it uses.)
- Pre-existing, untouched: `Vm::call_native` mishandles a native call whose last
  argument is a multi-result native call — `print(floor(1.5), floor(2.5),
  floor(3.5))` at top level prints `1 2 3 3.5`, and inside a loop it panicked
  with a slice-index error.

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
