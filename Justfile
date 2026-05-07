set shell := ["bash", "-c"]

# Run the lua dump script to generate bytecode files
dump:
    lua5.1 dump.lua

# Run lunacy against the dumped bytecode files
test: dump
    cargo run --features graph --bin lunacy

watch: dump
    cargo watch -- cargo check --bin lunacy

debug: dump
    RUST_LOG=all cargo run --features graph --bin lunacy -- dumped/dumped_20.bin

run benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo run --release --bin lunacy -- {{benchmark}}.bin

benchmarks: (run "binarytrees") (run "life") (run "queens")

hyperfine benchmark:
    luac5.1 -o {{benchmark}}.bin lua_benchmarking/benchmarks/{{benchmark}}/bench.lua
    cargo build --release --bin lunacy
    hyperfine --warmup 1 --export-markdown hyperfine-{{benchmark}}.md \
        "lua5.1 bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench" \
        "./target/release/lunacy {{benchmark}}.bin"

all: test benchmarks (hyperfine "binarytrees")
