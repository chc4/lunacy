set shell := ["bash", "-c"]
TEST_FEATURES := "counters graph jit gas gc_sanitize"

# Every test: `test`, then `test-stencils`.
tests: test test-stencils

# Run lunacy against the golden testcases
[env("RUST_BACKTRACE","1")]
test:
    # GC correctness tests
    cargo test "gc::" --features "gc_test,gc_sanitize" -- --test-threads 1
    # Normal interpreter tests
    cargo test --features "gc_sanitize"
    # Interpreter GC stress test
    cargo test --features "gc_stress gc_sanitize"
    # Golden suite with every block JIT compiled on first run (a debug build, so
    # window ops run through their interpreter path; `just test-stencils` runs
    # them as copied stencils)
    cargo test --features "immediate_jit gc_sanitize" --test golden_tests
    # Heap reset frees (no leak); needs the real finalizer, so runs without gc_sanitize
    cargo test --test gc_reset_frees

# Copy&patch window stencils (src/window.rs) as the JIT will use them: built
# with the `stencils` profile, optimized like release. The window unit
# tests also run in `just test` (debug); this runs them against optimized
# stencils, then the golden suite with `check_windows`: every window op the
# interpreter executes is also copy&patched and run natively, and the results
# must match. Then the golden suite with every block JIT compiled, so window ops
# run as copied stencils under the JIT's register allocation. (At opt-level 0,
# `NumericIntInt` keeps a jump table from the unfolded `match OP`, which the
# copier rejects: the check skips it and the JIT calls into the interpreter.)
STENCIL_OPT := "--profile stencils"
[env("RUST_BACKTRACE","1")]
test-stencils:
    cargo test --features check_windows --lib window:: {{STENCIL_OPT}}
    cargo test --features check_windows --test golden_tests {{STENCIL_OPT}}
    cargo test --features immediate_jit --test golden_tests {{STENCIL_OPT}}

# Runs of window residuals in a benchmark (docs/jit-register-cache.md): run it on
# the LBBV interpreter tier (every block entry counted, none hidden by the JIT)
# with the `graph` dump, then list each function's blocks with window runs,
# hottest first.
window-runs benchmark times='20':
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    rm -f func_*.dot func_*.pdf
    cargo run --release --no-default-features --features "lbbv graph" --bin bench -- {{benchmark}}.bin {{times}}
    python3 tools/window_runs.py func_*.dot

# The JIT's window allocation for a benchmark, in window_dump.txt: each compiled
# block's entry window, then per residual its loads, stores and moves, what each
# jump transfers, and the window after it.
window-dump benchmark times='20':
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo run --release --features window_dump --bin bench -- {{benchmark}}.bin {{times}}

# Save a benchmark's window dump as bench/window_dumps/<benchmark>.<name>.txt, a
# reference to compare window allocators against with `just window-dump-stats`.
window-dump-save benchmark name times='20':
    just window-dump {{benchmark}} {{times}}
    mkdir -p bench/window_dumps
    cp window_dump.txt bench/window_dumps/{{benchmark}}.{{name}}.txt

# A lua_tests program's window allocation under streaming allocation and each
# trace-building policy, as bench/window_dumps/<name>.<policy>.txt.
window-dump-policies name:
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    cargo build --release --features window_dump --bin lunacy
    mkdir -p bench/window_dumps
    for policy in streaming single unidirectional bidirectional; do LUNACY_TRACES=$policy ./target/release/lunacy {{name}}.bin > /dev/null && cp window_dump.txt bench/window_dumps/{{name}}.$policy.txt; done

# Executed loads, stores and moves of each benchmark, run `times` times, under
# streaming allocation and unidirectional traces, from their window dumps; a
# benchmark that fails (lunacy lacks some of Lua) says why.
window-dump-compare times +benchmarks:
    cargo build --release --features window_dump --bin bench
    for b in {{benchmarks}}; do luac5.1 -o $b.bin lua_benchmarking/benchmarks/$b/bench.lua || continue; for policy in streaming unidirectional; do if LUNACY_TRACES=$policy timeout 600 ./target/release/bench $b.bin {{times}} > /dev/null 2> target/window-dump-compare.err; then python3 tools/window_dump_stats.py --raw window_dump.txt | tail -1 | sed "s|^window_dump.txt|$b $policy|"; else echo "$b $policy: failed: $(grep -A1 -m1 panicked target/window-dump-compare.err | tail -1)"; fi; done; done

# The loads, stores and moves in window dumps, over all blocks and hot ones.
window-dump-stats *dumps='bench/window_dumps/*.txt':
    python3 tools/window_dump_stats.py {{dumps}}

[env("RUST_LOG", "debug")]
[env("RUST_BACKTRACE","1")]
test-debug:
    cargo test --features "gc_sanitize" -- --nocapture

watch:
    cargo watch -- cargo test

[env("RUST_LOG", "debug")]
debug name:
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    time cargo run --no-default-features --features "{{TEST_FEATURES}}" --bin lunacy -- {{name}}.bin

debug-jit name:
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    time cargo run --no-default-features --features "{{TEST_FEATURES}} immediate_jit" --bin lunacy -- {{name}}.bin

release name:
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    time cargo run --release --no-default-features --features "{{TEST_FEATURES}}" --bin lunacy -- {{name}}.bin

gdb-test name:
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    cargo build --release --bin lunacy
    gdb --args ./target/release/lunacy {{name}}.bin

# Benchmarks
run benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    time cargo run --release --bin bench -- {{benchmark}}.bin

[env("RUST_LOG", "debug")]
run-debug benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    time cargo run --bin bench -- {{benchmark}}.bin

graph name:
    luac5.1 -o {{name}}.bin {{name}}.lua
    cargo run --features graph --bin lunacy -- {{name}}.bin
graph-release name:
    luac5.1 -o {{name}}.bin {{name}}.lua
    cargo run --release --features graph --bin lunacy -- {{name}}.bin
gdb name:
    luac5.1 -o {{name}}.bin {{name}}.lua
    cargo build --release --bin lunacy
    gdb --args ./target/release/lunacy {{name}}.bin


baseline benchmark:
    time lua5.1 bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench

gdb-benchmark benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin bench
    gdb --args ./target/release/bench {{benchmark}}.bin

flamegraph benchmark times='10':
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    -rm /tmp/perf-*.map
    cargo flamegraph --features "perf" --bin bench -- {{benchmark}}.bin {{times}}
    -firefox -new-tab flamegraph.svg

benchmarks: (run "binarytrees") (run "life") (run "nbody")

# Interpreter
INTERPRETER_FEATURES := "magic"
interpreter-compile:
    cargo build --release --no-default-features --features "{{INTERPRETER_FEATURES}}" --bin bench --target-dir ./target/interpreter
interpreter benchmark: interpreter-compile
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    time ./target/interpreter/release/bench {{benchmark}}.bin
interpreter-test name: interpreter-compile
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    time ./target/interpreter/release/bench {{name}}.bin

# Unsafe
unsafe-compile:
    cargo build --profile unsafe --no-default-features --features unsafe --bin bench \
        -Z build-std="core,std,panic_abort"
unsafe benchmark: unsafe-compile
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    time ./target/unsafe/bench {{benchmark}}.bin

gdb-unsafe benchmark: unsafe-compile
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    gdb --args ./target/unsafe/bench {{benchmark}}.bin


# Hyperfine reports
hyperfine benchmark times='10': unsafe-compile interpreter-compile
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin bench
    hyperfine --warmup 1 --export-markdown hyperfine-{{benchmark}}.md \
        "lua5.1 bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench {{times}}" \
        "./target/interpreter/release/bench {{benchmark}}.bin {{times}}" \
        "./target/release/bench {{benchmark}}.bin {{times}}" \
        "./target/unsafe/bench {{benchmark}}.bin {{times}}"
# Compare the trace-building policies of the window allocator, and streaming
# allocation, on a benchmark
# (LUNACY_TRACES; see docs/trace-register-allocation.md).
hyperfine-traces benchmark times='10' policies='streaming,single,unidirectional,bidirectional':
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin bench
    hyperfine --warmup 1 --export-markdown hyperfine-{{benchmark}}-{{times}}-traces.md -L policy {{policies}} \
        "LUNACY_TRACES={policy} ./target/release/bench {{benchmark}}.bin {{times}}"
# `hyperfine-traces` over the benchmarks lunacy runs, each run enough times for
# a stable mean. life runs twice: the difference between its 1000 and 5000 runs
# is the steady-state cost of the code, the rest the upfront cost (compiling).
hyperfines-traces policies='streaming,unidirectional,bidirectional': (hyperfine-traces "life" "1000" policies) (hyperfine-traces "life" "5000" policies) (hyperfine-traces "nbody" "10" policies) (hyperfine-traces "queens" "3000" policies) (hyperfine-traces "fannkuch_redux" "150" policies)

# mimalloc's statistics for a benchmark under each trace policy, before and
# after the heap's final reset (feature `alloc_stats`), each policy's in
# target/alloc-stats-<benchmark>-<policy>.txt.
alloc-stats benchmark times='10' policies='streaming unidirectional':
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --features alloc_stats --bin bench
    for policy in {{policies}}; do LUNACY_TRACES=$policy ./target/release/bench {{benchmark}}.bin {{times}} > /dev/null 2> target/alloc-stats-{{benchmark}}-$policy.txt; echo "target/alloc-stats-{{benchmark}}-$policy.txt"; done

# Compare this checkout's release build against revision `ref`'s on one
# benchmark: `ref` is built in a detached worktree under target/compare/ (kept
# for reruns, its submodules linked to this checkout's).
hyperfine-vs ref benchmark times='10':
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin bench
    test -d target/compare/{{ref}} || git worktree add --detach target/compare/{{ref}} {{ref}}
    git -C target/compare/{{ref}} checkout --detach {{ref}}
    for module in dynasm-rs memmap2-rs; do test -L target/compare/{{ref}}/$module || { rmdir target/compare/{{ref}}/$module && ln -s "$(realpath $module)" target/compare/{{ref}}/$module; }; done
    cd target/compare/{{ref}} && cargo build --release --bin bench
    hyperfine --warmup 1 --export-markdown hyperfine-{{benchmark}}-vs-{{ref}}.md \
        "target/compare/{{ref}}/target/release/bench {{benchmark}}.bin {{times}}" \
        "./target/release/bench {{benchmark}}.bin {{times}}"
hyperfine-jit benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin bench
    hyperfine --warmup 1 --export-markdown hyperfine-{{benchmark}}-jit.md \
        "./target/release/bench {{benchmark}}.bin"
hyperfine-unsafe benchmark: unsafe-compile
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    hyperfine --warmup 1 --export-markdown hyperfine-{{benchmark}}-unsafe.md \
        "./target/unsafe/bench {{benchmark}}.bin"


hyperfines: (hyperfine "binarytrees") (hyperfine "life") (run "nbody")

all: test benchmarks (hyperfine "binarytrees")
