set shell := ["bash", "-c"]

# Run the lua dump script to generate bytecode files
dump:
    lua5.1 dump.lua

# Run lunacy against the dumped bytecode files
test-dumped: dump
    cargo run --release --bin lunacy

# Compile and run binarytrees benchmark
bench-binarytrees:
    luac5.1 -o dumped/binarytrees.bin lua_benchmarking/benchmarks/binarytrees/bench.lua
    cargo run --release --bin lunacy -- dumped/binarytrees.bin

# Compile and run life benchmark
bench-life:
    luac5.1 -o life.bin lua_benchmarking/benchmarks/life/bench.lua
    cargo run --release --bin lunacy -- life.bin

# Run hyperfine benchmark comparing lua5.1 and lunacy (using binarytrees)
hyperfine:
    luac5.1 -o dumped/binarytrees.bin lua_benchmarking/benchmarks/binarytrees/bench.lua
    cargo build --release --bin lunacy
    hyperfine --warmup 1 --export-markdown hyperfine.md \
        "lua5.1 bench.lua -- lua_benchmarking/benchmarks/binarytrees/bench" \
        "./target/release/lunacy dumped/binarytrees.bin"

# Run all tests and benchmarks
all: test-dumped bench-binarytrees bench-life
