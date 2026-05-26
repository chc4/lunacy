| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.160 ± 0.026 | 4.113 | 4.191 | 1.00 |
| `./target/interpreter/release/bench nbody.bin` | 11.501 ± 0.047 | 11.417 | 11.584 | 2.76 ± 0.02 |
| `./target/release/bench nbody.bin` | 4.586 ± 0.049 | 4.534 | 4.676 | 1.10 ± 0.01 |
| `./target/unsafe/bench nbody.bin` | 4.170 ± 0.061 | 4.091 | 4.263 | 1.00 ± 0.02 |
