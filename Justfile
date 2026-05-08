set shell := ["bash", "-c"]

# Run the lua dump script to generate bytecode files
dump:
    lua5.1 dump.lua

# Run lunacy against the dumped bytecode files
test: dump
    cargo run --features graph --bin lunacy

watch: dump
    cargo watch -- cargo check --bin lunacy

[env("RUST_LOG", "debug")]
debug: dump
    cargo run --no-default-features --features "graph counters jit immediate_jit" --bin lunacy -- ./dumped/dumped_12.bin

# Benchmarks
run benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    time cargo run --release --bin lunacy -- {{benchmark}}.bin

graph benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    time cargo run --release --features graph --bin lunacy -- {{benchmark}}.bin

baseline benchmark:
    time lua5.1 bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench

benchmarks: (run "binarytrees") (run "life") (run "nbody")

# Hyperfine reports
hyperfine benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin lunacy
    hyperfine --warmup 1 --export-markdown hyperfine-{{benchmark}}.md \
        "lua5.1 bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench" \
        "./target/release/lunacy {{benchmark}}.bin"
hyperfines: (hyperfine "binarytrees") (hyperfine "life") (run "nbody")

all: test benchmarks (hyperfine "binarytrees")
