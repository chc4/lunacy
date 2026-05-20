| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.150 ± 0.032 | 4.079 | 4.178 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 12.815 ± 0.024 | 12.771 | 12.850 | 3.09 ± 0.02 |
| `./target/release/lunacy nbody.bin` | 5.330 ± 0.066 | 5.215 | 5.474 | 1.28 ± 0.02 |
| `./target/unsafe/lunacy nbody.bin` | 4.850 ± 0.074 | 4.691 | 4.957 | 1.17 ± 0.02 |
