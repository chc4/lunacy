| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.148 ± 0.036 | 4.077 | 4.185 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 14.814 ± 0.051 | 14.730 | 14.925 | 3.57 ± 0.03 |
| `./target/release/lunacy nbody.bin` | 6.480 ± 0.028 | 6.452 | 6.550 | 1.56 ± 0.02 |
| `./target/unsafe/lunacy nbody.bin` | 5.883 ± 0.038 | 5.839 | 5.960 | 1.42 ± 0.02 |
