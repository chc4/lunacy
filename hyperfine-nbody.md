| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.153 ± 0.018 | 4.107 | 4.171 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 14.181 ± 0.219 | 14.013 | 14.764 | 3.41 ± 0.05 |
| `./target/release/lunacy nbody.bin` | 8.512 ± 0.061 | 8.419 | 8.635 | 2.05 ± 0.02 |
| `./target/unsafe/release/lunacy nbody.bin` | 8.165 ± 0.138 | 8.044 | 8.505 | 1.97 ± 0.03 |
