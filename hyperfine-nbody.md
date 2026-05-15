| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.156 ± 0.029 | 4.100 | 4.186 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 11.310 ± 0.052 | 11.247 | 11.410 | 2.72 ± 0.02 |
| `./target/release/lunacy nbody.bin` | 6.251 ± 0.029 | 6.205 | 6.302 | 1.50 ± 0.01 |
| `./target/unsafe/lunacy nbody.bin` | 5.605 ± 0.024 | 5.572 | 5.643 | 1.35 ± 0.01 |
