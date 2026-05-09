| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.165 ± 0.040 | 4.084 | 4.228 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 14.298 ± 0.063 | 14.183 | 14.393 | 3.43 ± 0.04 |
| `./target/release/lunacy nbody.bin` | 8.865 ± 0.073 | 8.802 | 9.034 | 2.13 ± 0.03 |
| `./target/unsafe/release/lunacy nbody.bin` | 8.283 ± 0.203 | 8.073 | 8.805 | 1.99 ± 0.05 |
