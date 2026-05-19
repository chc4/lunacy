# Lunacy

Lunacy is a Rust implementation of Lua 5.1. It doesn't contain a compiler frontend, and instead parses dumped bytecode from PUC Lua.

# JIT
Lunacy, unlike most other Rust Lua implementations, contains a Just-In-Time compiler. It uses [Lazy Basic Block Versioning] in order to specialize bytecode operations based on runtime types, and then uses [DynASM-rs] for a template JIT for those specialized operations. The LBBV specializer implements table shape optimization, which allows for most Lua functions to use `O(1)` table key accesses. This scheme is mostly novel, but is based on LuaJIT's [hash slot specialization] modified to be usable for a non-tracing JIT.

## Benchmarks
The normal interpreter mode for Lunacy is unfortunately fairly slow currently (~3x slower than PUC Lua). However the JIT, with the `unsafe` feature enabled to skip runtime bounds checks plus the `skip_rc` feature to replace our current `Rc<T>` garbage collection with "leak everything", is able to run slightly faster than PUC Lua on [nbody](hyperfine-nbody.md).

# Using
We use [just] for workflow automation.

* `just test` will run some simple self-tests from `dump.lua` for quick language semantics validation.
* `just run <bench>` will run the given benchmark using the release profile.
* `just hyperfine <bench>` will generate a [hyperfine] report for the given benchmark with PUC Lua, the interpreter-only mode of Lunacy, the `release` profile, and an `unsafe` profile (which disables bounds checking for some structures).
* `just flamegraph <bench>` will generate a `cargo-flamegraph` performance report. Lunacy supports emitting a perf map file so it can track JIT times, although the lack of frame pointers means its not very good.

[Lazy Basic Block Versioning]: https://arxiv.org/abs/1411.0352
[DynASM-rs]: https://github.com/CensoredUsername/dynasm-rs
[hash slot specialization]: https://lua-users.org/lists/lua-l/2009-11/msg00089.html
[just]: https://github.com/casey/just
[hyperfine]: https://github.com/sharkdp/hyperfine
[cargo-flamegraph]: https://github.com/ferrous-systems/cargo-flamegraph
