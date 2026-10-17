# Upvalue effects: ideas from the uxn emulator profile

Not started. Neither idea below speeds up the uxn benchmarks on its own.

## Why the bitwise emulator doesn't gain from upvalue paths

Steady state (`just jit-profile uxn_bit_fib 10`), the bit ops are ~3.7% and
native identity guards ~2.6% of samples. The cost is the emulator's dispatch
loop, `op[ins](wst, rst)` in varvara/uxn_bit.lua's `eval`, which is genuinely
polymorphic:

- upvalue reloads (`window(GetUpval)`) ~11%: after every call the loop reloads
  `ram`, `pc`, `op`, `ret`, `wst` and `rst`, as a callee may have set some
  upvalue (ops do set `pc`), and `Effects::UPVALUE` drops every upvalue fact;
- type guards ~12.5%, dynamic guards ~7.6%, `dynamic_call`, `call_lua` and
  `nil_slots` ~11%;
- closed-upvalue stores ~8%: every write of `pc`, a closed cell, takes
  `SetUpval`'s out-of-line path (`set_closed`, for the write barrier).

md5 gains because its helpers are direct calls, which inline and receive the
caller's facts; the emulator's callee comes out of a table each instruction.

## Idea 1: split `Effects::UPVALUE` into open and closed writes

Sound because a cell's open or closed state belongs to the cell: a cell open in
the caller (its captured slots, Note [Captured slots]) stays open for the whole
call, its frame being below the caller's, and a closed cell never reopens, so a
callee's write to a closed cell is to none the caller has open, nor to its
stack slots.

- `Effects`: `OPEN_UPVALUE` and `CLOSED_UPVALUE` bits.
- `SetUpval`: open and closed as the two ways of an optimistic op, as the chain
  loads are, rather than a branch in its stencil and `set_closed` on the
  rejoin; each way yields its own `SetUpvalue` effect. The closed way is
  compiled, its bit joining the prototype's effects, before it first runs, so
  the join still covers everything that ran (Note [Call effects]). First-seen
  layout makes closed the hot way for a module-level function.
- `Effects::apply`: `CLOSED_UPVALUE` alone drops upvalue facts but keeps the
  caller's captured slots' types; `OPEN_UPVALUE` does what `UPVALUE` does.
- Helps a function with local helper closures (open cells) calling code that
  updates module-level state. Not the emulator: `eval` captures no slots, and
  every fact it loses is about a closed cell.

## Idea 2: never-reassigned upvalues (what would help the emulator)

`ram`, `op`, `ret`, `wst`, `rst`, `band` and the rest are assigned once, when
captured, and never again; only `pc` (and `dei` and `deo`, once, in
`set_devices`) is reassigned. At a chunk's load, find the captured locals that
no SETUPVAL of any nested prototype targets and whose register isn't written
after the CLOSURE capturing it: facts about their cells survive any call, a
generic one too. This is the common `local band = bit.band` and module-state
pattern.

Or exact cell identity through a callee's identity guard, as the guarded
closure fixes its upvalues' cells: a continuation after a known callee drops
the facts of only the cells it set. This needs the callee guarded.

## Separately

The closed-upvalue store's out-of-line path (~8% here) costs any
interpreter-style Lua program that keeps its state in upvalues, whichever way
the facts go.
