set shell := ["bash", "-c"]

# Run the lua dump script to generate bytecode files
dump:
    lua5.1 dump.lua

# Run lunacy against the dumped bytecode files
test: dump
    cargo run --features graph --bin lunacy

watch: dump
    cargo watch -- cargo check --bin lunacy

TEST_FEATURES := "counters graph jit gas"
[env("RUST_LOG", "debug")]
debug num: dump
    time cargo run --no-default-features --features "{{TEST_FEATURES}}" --bin lunacy -- ./dumped/dumped_{{num}}.bin

debug-jit num: dump
    time cargo run --no-default-features --features "{{TEST_FEATURES}} immediate_jit" --bin lunacy -- ./dumped/dumped_{{num}}.bin

release num: dump
    time cargo run --release --no-default-features --features "{{TEST_FEATURES}}" --bin lunacy -- ./dumped/dumped_{{num}}.bin

gdb-test num: dump
    cargo build --release --bin lunacy
    gdb --args ./target/release/lunacy ./dumped/dumped_{{num}}.bin

testing: (debug "12")

# Benchmarks
run benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    time cargo run --release --bin lunacy -- {{benchmark}}.bin

[env("RUST_LOG", "debug")]
run-debug benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    time cargo run --bin lunacy -- {{benchmark}}.bin

graph name:
    luac5.1 -o {{name}}.bin {{name}}.lua
    cargo run --features graph --bin lunacy -- {{name}}.bin
graph-release name:
    luac5.1 -o {{name}}.bin {{name}}.lua
    cargo run --release --features graph --bin lunacy -- {{name}}.bin

baseline benchmark:
    time lua5.1 bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench

gdb-benchmark benchmark: dump
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin lunacy
    gdb --args ./target/release/lunacy {{benchmark}}.bin


benchmarks: (run "binarytrees") (run "life") (run "nbody")

# Interpreter
INTERPRETER_FEATURES := "magic"
interpreter-compile:
    cargo build --release --no-default-features --features "{{INTERPRETER_FEATURES}}" --bin lunacy --target-dir ./target/interpreter
interpreter benchmark: interpreter-compile
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    time ./target/interpreter/release/lunacy {{benchmark}}.bin
interpreter-test num: interpreter-compile dump
    time ./target/interpreter/release/lunacy ./dumped/dumped_{{num}}.bin

# Unsafe
unsafe-compile:
    cargo build --profile unsafe --no-default-features --features unsafe --bin lunacy \
        -Z build-std="core,std,panic_abort"
unsafe benchmark: unsafe-compile
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    time ./target/unsafe/lunacy {{benchmark}}.bin

gdb-unsafe benchmark: unsafe-compile
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    gdb --args ./target/unsafe/lunacy {{benchmark}}.bin


# Hyperfine reports
hyperfine benchmark: unsafe-compile interpreter-compile
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin lunacy
    hyperfine --warmup 1 --export-markdown hyperfine-{{benchmark}}.md \
        "lua5.1 bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench" \
        "./target/interpreter/release/lunacy {{benchmark}}.bin" \
        "./target/release/lunacy {{benchmark}}.bin" \
        "./target/unsafe/lunacy {{benchmark}}.bin"
hyperfine-jit benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin lunacy
    hyperfine --warmup 1 --export-markdown hyperfine-{{benchmark}}-jit.md \
        "./target/release/lunacy {{benchmark}}.bin"
hyperfine-unsafe benchmark: unsafe-compile
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    hyperfine --warmup 1 --export-markdown hyperfine-{{benchmark}}-unsafe.md \
        "./target/unsafe/lunacy {{benchmark}}.bin"


hyperfines: (hyperfine "binarytrees") (hyperfine "life") (run "nbody")

all: test benchmarks (hyperfine "binarytrees")
