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
- **JIT mode** (`src/window_alloc.rs`, `Note [Window allocation]`; to be replaced
  by the streaming allocator proposed in section 6): `Storage` only records its
  token; the op, with all of its operands known, is placed at
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
allocates each run of window residuals (see `Note [Window allocation]`; its
allocation is to be replaced, see section 6);
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
closure, sharing the store with the window op. In release a get's stencil is a
20-instruction hot path with no calls (witness bounds check, table tag check,
entry index check, load, `jmp` to the continuation); its only relocations are
its cold panic paths. `just test-stencils` builds with the `stencils` profile,
every package optimized, so its stencils match release (7 relocations for a
get, all cold). Both copy at every `SKIP`. The multi-op runs nbody's `advance`
executes in its steady state (counted per block), worked by hand for the
8-register window (loads/stores/moves; loads and stores at the floor):

| run | now | with the table ops as `Exec`s |
|---|---|---|
| `bi.vz = bivz; bi.x = bix + dt*bivx; bi.y = ...; bi.z = ...; i += step` (11 ops) | 10/2/4 | — |
| `dx = bix - bj.x` | 2/1/0 | 3/2 |
| `dz = biz - bj.z; dist2 = ...` | 4/3/5 | 5/4 |
| `bm = bj.mass * mag; bivx -= dx * bm; ...` | 9/5/4 | 10/6 |
| `bj.vx = bj.vx + dx * bm` | 3/2/2 | 5/3 |
| ... plus `j += step` | 5/3/2 | 7/4 |
| `mag = dt / (mag * dist2)` | 3/2/0 | 3/2 |

In `bj.vx = bj.vx + dx * bm` both moves are forced by the window's shape: the
got value must sit right before the product, whose op covers the register the
get left it in, and `bj` must sit right before the sum. In the 11-op run each
of the three `bi.? = t` stores needs `bi` copied in right before `t` (3 moves)
and `bivz` moves beside `dt` (1). The allocator matches every row; its tests pin
them, and the exhaustive sweep covers all three op shapes.

The `bi` run is long because `bi` keeps its shape (a key already cached in the
slot's `CType::Shape` costs an epoch check, not an `href_init`). The `bj` runs
are short because the inner loop's `bj = bodies[j]` is an array get that
resets slot 19 to plain `Table`, dropping the shape, so each field of each new
`bj` runs `href_init` + `select` (a runtime key lookup and a block split) every
iteration; likewise `bi = bodies[i]` in the outer loop.

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
- Longer `bj` runs need the array get `bodies[j]` to yield a guardable shape
  (all bodies share one), so its fields cost an epoch/shape check instead of an
  `href_init` + block split per field per iteration: a specializer change.
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

---

## 6. Register allocation: a streaming forward pass (proposal, for review)

This replaces the allocator in `src/window_alloc.rs`. That one spends compile
time on placement quality inside one run: a backward scan for next uses,
relocating displaced values into spare registers, ranking evictions, and a
lookahead. That is the wrong trade for a JIT, and within one block it matters
little when we compile a tree of blocks.

### What copy-and-patch does (Xu & Kjolstad, OOPSLA 2021, §3–4)

- "we repurpose the function prototype and the calling convention as a register
  allocation protocol, where each function parameter implicitly corresponds to
  some physical register". A value that must survive a stencil is a
  **pass-through parameter**, passed "from the argument to the continuation
  verbatim". That is our window, and `SKIP` is the number of pass-through
  registers below an op.
- Registers hold expression temporaries only: "we only use registers to
  preserve temporary values produced while evaluating an expression". Locals
  live in memory.
- One forward pass, "a post-order traversal of the AST to abstractly evaluate
  the expression", over "the stack of outstanding temporary operands". An op
  takes its operands from the top of that stack and pushes its result. It is "a
  simplified version of the Simple Sethi-Ullman Algorithm that does not choose
  between the orders of evaluating a node's children", chosen for "its very low
  overhead and little loss of practical effectiveness". Temporaries beyond the
  register budget spill to stack slots, and temporaries live across a call are
  spilled, since the callee gets every register.
- Quality is deliberately secondary: a mem2reg pass gave "up to 10% execution
  performance boost, but results in about 33× slower compilation. We deemed this
  trade-off as not worthwhile."

### What carries over

The stack discipline rests on two properties of AST temporaries that our
operands lack:

1. A temporary is used once, so an op's operands die at the op and its result
   can take their place. Lua slots are registers of a register machine: `bm` is
   read three times in one run, and locals are read throughout a block.
2. The result overwrites the operands' registers. Our inputs are read-only: an op
   never overwrites the register of a slot it reads, so a cached slot's register
   only ever holds that slot's value.

So we take the **streaming** part and not the exact stack discipline:

- one forward pass, during codegen;
- a few register comparisons of work per op;
- no lookahead, and no analysis of the run or of the block tree beforehand.

### Operand order belongs to the op

`windowed!` declares one ordered operand list, each operand marked as an input
or an output, e.g. `(out c, a, b)`. Operand `i` is window register `SKIP + i`.
The emit site yields its `Storage`s in the same order. The allocator knows only
each operand's index and whether it is read or written, so it handles any order
an op names:

- `NumericIntInt` would declare `[dest, lhs, rhs]`, so a result lands below
  where the next op's inputs go;
- `GetTableHref` would declare `[dest, table]`;
- `SetTableHref` would declare `[table, value]`.

`window::position` goes away.

### The allocator

State, carried from op to op:

- `regs[0..WINDOW]`: the slot whose current value each register caches, if any;
- `dirty`: cached slots whose stack home is stale.

There is no liveness. Every cached value is only a cache: overwriting a clean
one drops it, and a later read reloads it; overwriting a dirty one stores it
first.

`Storage` records its token and decides nothing. At an `ExecWindow` with operands
`o_0..o_{n-1}`:

1. **Pick `SKIP`** from `0..=WINDOW-n`, the cheapest by what it would emit:
   - an input already in its register costs nothing;
   - an input cached in another register costs a move;
   - an uncached input costs a load;
   - a dirty value in the span costs a store, unless it is an older value of
     one of the op's outputs, which the op rewrites.

   Ties go to the `SKIP` whose span overwrites the fewest cached values, then to
   the lowest. That is `WINDOW × n` register comparisons (8 × 3 for a numeric
   op).
2. **Emit**, in this order:
   - the stores;
   - the moves and loads into the span, as one parallel move (reads before
     writes, cycles through the scratch register);
   - the stencil.
3. **Update**: each output is cached, dirty, in its register, and other copies of
   its slot's older value are dropped.

At a flush point (any residual other than `Storage`/`ExecWindow`), store every
dirty register. Calls clobber every register, so the cache is emptied too.

**What it gives up, worked by hand** on nbody's steady-state 11-op run
`bi.vz = bivz; bi.x = bix + dt*bivx; bi.y = ...; bi.z = ...; i += step` in 8
registers, with ops in `[out, in, ...]` order:

- The first `dt*bivx` takes free registers (`t15`, `dt`, `bivx` at `w2..w4`).
- `bix + t15` then runs at 0 to read `t15` in place, which overwrites the
  cached `bi` and `bivz`.
- The first `bi.x = t15` reloads `bi`.
- Each later group finds `dt` still at `w3` and `bi` at `w5`, so it needs one
  move (for `t15`) per store.

That comes to 12 loads, 2 stores and 3 moves. The floor is 10 loads and 2
stores, and the best plan (a search) does 10/2/2. The nbody tests would pin
the counts the streaming rule gives, worked by hand like this. The
symbolic-machine correctness checks and the exhaustive sweep stay.

### Code changes

- **`windowed!`:** the ordered operand list with in/out markers. The emit sites
  yield their `Storage`s in that order. `window::position` goes.
- **`window_alloc`:** the streaming allocator above replaces `begin`'s
  next-use scan, the placement search, relocation and eviction ranking.
  - `begin` shrinks to resetting the state; there is nothing to precompute.
  - `op` takes the op's usable `SKIP`s from the copier directly.
  - The JIT keeps calling `storage` / `op` / `flush`.
- **Not in this change:** LuaJIT-style bottom-up assignment over the compiled
  region. That would be a backward pass over the transitive closure of blocks
  before codegen, storing each token's register compactly for the forward pass.
  It would place values better across blocks, but costs a pass over the region
  and the storage for its results. The paper suggests the streaming pass is the
  right first step; revisit with measurements.

### Decisions for review

1. **Cache every slot, or only expression temporaries** as the paper does. In
   Lua bytecode the temporaries are the slots at and above the active locals,
   allocated like a stack (luac's `freereg`). Knowing that per pc needs each
   prototype's active-local count, which stripped debug info may lack. The
   design above caches every slot and needs nothing extra.
2. **Across blocks:** carry the cache along straightline successor edges from the
   start (section 2, rule 2), or flush at every block boundary first and add
   the carry afterwards.
3. **In-place updates:** whether an output may share an input's register when both
   name the same slot. That is an in-place update like `t = bix + t`, the paper's
   "result replaces the operand", and it would need its own stencil variant.
   Not proposed now.
