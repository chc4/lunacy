| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.149 ± 0.044 | 4.079 | 4.200 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 14.252 ± 0.139 | 14.111 | 14.580 | 3.43 ± 0.05 |
| `./target/release/lunacy nbody.bin` | 6.911 ± 0.044 | 6.854 | 7.005 | 1.67 ± 0.02 |
| `./target/unsafe/lunacy nbody.bin` | 6.208 ± 0.018 | 6.185 | 6.240 | 1.50 ± 0.02 |
