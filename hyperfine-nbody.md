| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.167 ± 0.026 | 4.101 | 4.193 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 14.103 ± 0.091 | 14.005 | 14.276 | 3.38 ± 0.03 |
| `./target/release/lunacy nbody.bin` | 6.222 ± 0.042 | 6.172 | 6.319 | 1.49 ± 0.01 |
| `./target/unsafe/lunacy nbody.bin` | 5.813 ± 0.031 | 5.780 | 5.865 | 1.39 ± 0.01 |
