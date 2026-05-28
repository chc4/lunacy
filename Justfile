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

baseline benchmark:
    time lua5.1 bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench

gdb-benchmark benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin bench
    gdb --args ./target/release/bench {{benchmark}}.bin

flamegraph benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    -rm /tmp/perf-*.map
    cargo flamegraph --features "perf" --bin bench -- {{benchmark}}.bin
    firefox -new-tab flamegraph.svg

benchmarks: (run "binarytrees") (run "life") (run "nbody")

dump-ir name:
    luac5.1 -o {{name}}.bin {{name}}.lua
    cargo run --release --features "jit_dump counters" --bin lunacy -- {{name}}.bin

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
hyperfine benchmark: unsafe-compile interpreter-compile
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin bench
    hyperfine --warmup 1 --export-markdown hyperfine-{{benchmark}}.md \
        "lua5.1 bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench" \
        "./target/interpreter/release/bench {{benchmark}}.bin" \
        "./target/release/bench {{benchmark}}.bin" \
        "./target/unsafe/bench {{benchmark}}.bin"
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
