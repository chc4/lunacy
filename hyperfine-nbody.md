| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.151 ± 0.038 | 4.073 | 4.182 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 14.885 ± 0.103 | 14.777 | 15.100 | 3.59 ± 0.04 |
| `./target/release/lunacy nbody.bin` | 6.329 ± 0.036 | 6.286 | 6.396 | 1.52 ± 0.02 |
| `./target/unsafe/lunacy nbody.bin` | 5.697 ± 0.025 | 5.669 | 5.740 | 1.37 ± 0.01 |
