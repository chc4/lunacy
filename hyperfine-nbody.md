| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.161 ± 0.039 | 4.084 | 4.190 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 13.246 ± 0.023 | 13.212 | 13.280 | 3.18 ± 0.03 |
| `./target/release/lunacy nbody.bin` | 8.523 ± 0.213 | 7.945 | 8.683 | 2.05 ± 0.05 |
| `./target/unsafe/lunacy nbody.bin` | 7.504 ± 0.117 | 7.384 | 7.735 | 1.80 ± 0.03 |
