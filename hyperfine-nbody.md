| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.126 ± 0.037 | 4.075 | 4.168 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 12.819 ± 0.062 | 12.719 | 12.916 | 3.11 ± 0.03 |
| `./target/release/lunacy nbody.bin` | 5.315 ± 0.062 | 5.218 | 5.380 | 1.29 ± 0.02 |
| `./target/unsafe/lunacy nbody.bin` | 4.891 ± 0.084 | 4.758 | 5.045 | 1.19 ± 0.02 |
