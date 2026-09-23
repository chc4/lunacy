set shell := ["bash", "-c"]
TEST_FEATURES := "counters graph jit gas gc_sanitize"

# Run lunacy against the golden testcases
[env("RUST_BACKTRACE","1")]
test:
    # GC correctness tests
    cargo test "gc::" --features "gc_test,gc_sanitize" -- --test-threads 1
    # Normal interpreter tests
    cargo test --features "gc_sanitize"
    # Interpreter GC stress test
    cargo test --features "gc_stress gc_sanitize"
    # Golden suite with every block JIT compiled on first run
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
