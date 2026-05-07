set shell := ["bash", "-c"]

# Run the lua dump script to generate bytecode files
dump:
    lua5.1 dump.lua

# Run lunacy against the dumped bytecode files
test: dump
    cargo run --release --bin lunacy

watch: dump
    cargo watch -- cargo check --bin lunacy

debug: dump
    RUST_LOG=all cargo run --bin lunacy -- dumped/dumped_20.bin

# Compile and run binarytrees benchmark
binarytrees:
    luac5.1 -o binarytrees.bin lua_benchmarking/benchmarks/binarytrees/bench.lua
    cargo run --release --bin lunacy -- binarytrees.bin

# Compile and run life benchmark
life:
    luac5.1 -o life.bin lua_benchmarking/benchmarks/life/bench.lua
    cargo run --release --bin lunacy -- life.bin
life-debug:
    luac5.1 -o life.bin lua_benchmarking/benchmarks/life/bench.lua
    cargo run --bin lunacy -- life.bin
life-baseline:
    lua5.1 bench.lua -- lua_benchmarking/benchmarks/life/bench


hyperfine:
    luac5.1 -o binarytrees.bin lua_benchmarking/benchmarks/binarytrees/bench.lua
    cargo build --release --bin lunacy
    hyperfine --warmup 1 --export-markdown hyperfine.md \
        "lua5.1 bench.lua -- lua_benchmarking/benchmarks/binarytrees/bench" \
        "./target/release/lunacy binarytrees.bin"

all: test hyperfine
