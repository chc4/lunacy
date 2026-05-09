| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.142 ± 0.038 | 4.092 | 4.196 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 13.908 ± 0.147 | 13.698 | 14.256 | 3.36 ± 0.05 |
| `./target/release/lunacy nbody.bin` | 8.999 ± 0.039 | 8.945 | 9.084 | 2.17 ± 0.02 |
| `./target/unsafe/release/lunacy nbody.bin` | 8.240 ± 0.142 | 8.119 | 8.608 | 1.99 ± 0.04 |
