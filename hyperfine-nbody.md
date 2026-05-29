| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench 10` | 4.153 ± 0.038 | 4.083 | 4.190 | 1.01 ± 0.02 |
| `./target/interpreter/release/bench nbody.bin 10` | 11.405 ± 0.082 | 11.213 | 11.519 | 2.77 ± 0.04 |
| `./target/release/bench nbody.bin 10` | 4.551 ± 0.036 | 4.495 | 4.593 | 1.11 ± 0.02 |
| `./target/unsafe/bench nbody.bin 10` | 4.116 ± 0.051 | 4.034 | 4.183 | 1.00 |
