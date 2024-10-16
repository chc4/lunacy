# Lunacy

Lua 5.1 interpeter. It doesn't have the compiler frontend, just parses dumped bytecode from PUC Lua.

## Benchmarks
PUC Lua:
> export TESTCASE=lua_benchmarking/benchmarks/nbody/bench && time lua bench.lua -- $TESTCASE

> lua bench.lua -- $TESTCASE  3.73s user 0.00s system 99% cpu 3.763 total

Lunacy:
> export TESTCASE=lua_benchmarking/benchmarks/nbody/bench && cargo build --release --bin=lunacy && time ./target/release/lunacy $TESTCASE.bin

> RUST_LOG=debug ./target/release/lunacy $TESTCASE.bin  8.88s user 0.00s system 99% cpu 8.892 total

so yeah it's kinda slow
