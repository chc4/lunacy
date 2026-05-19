| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.169 ± 0.065 | 4.086 | 4.321 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 12.905 ± 0.074 | 12.774 | 13.033 | 3.10 ± 0.05 |
| `./target/release/lunacy nbody.bin` | 5.547 ± 0.044 | 5.475 | 5.636 | 1.33 ± 0.02 |
| `./target/unsafe/lunacy nbody.bin` | 5.026 ± 0.088 | 4.892 | 5.184 | 1.21 ± 0.03 |
