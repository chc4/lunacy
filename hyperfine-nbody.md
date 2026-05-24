| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.163 ± 0.032 | 4.097 | 4.193 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 12.671 ± 0.035 | 12.630 | 12.757 | 3.04 ± 0.02 |
| `./target/release/lunacy nbody.bin` | 5.262 ± 0.043 | 5.188 | 5.340 | 1.26 ± 0.01 |
| `./target/unsafe/lunacy nbody.bin` | 4.877 ± 0.028 | 4.828 | 4.906 | 1.17 ± 0.01 |
