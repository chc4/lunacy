| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.162 ± 0.023 | 4.114 | 4.187 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 13.642 ± 0.074 | 13.552 | 13.760 | 3.28 ± 0.03 |
| `./target/release/lunacy nbody.bin` | 7.884 ± 0.071 | 7.803 | 8.015 | 1.89 ± 0.02 |
| `./target/unsafe/lunacy nbody.bin` | 7.484 ± 0.081 | 7.376 | 7.633 | 1.80 ± 0.02 |
