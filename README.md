# Lunacy

Lua 5.1 interpeter. It doesn't have the compiler frontend, just parses dumped bytecode from PUC Lua.

## Benchmarks
PUC Lua:
> time lua lua_benchmarking/benchmarks/nbody/bench.lua
> lua lua_benchmarking/benchmarks/nbody/bench.lua  0.37s user 0.00s system 99% cpu 0.372 total

Lunacy:
> export TESTCASE=lua_benchmarking/benchmarks/nbody/bench && cargo build --release --bin=lunacy && time ./target/release/lunacy $TESTCASE.bin
> ./target/release/lunacy $TESTCASE.bin  1.56s user 0.00s system 99% cpu 1.569 total

so yeah it's kinda slow
