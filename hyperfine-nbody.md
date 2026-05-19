| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.173 ± 0.070 | 4.122 | 4.364 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 12.956 ± 0.150 | 12.787 | 13.273 | 3.10 ± 0.06 |
| `./target/release/lunacy nbody.bin` | 5.500 ± 0.035 | 5.441 | 5.565 | 1.32 ± 0.02 |
| `./target/unsafe/lunacy nbody.bin` | 5.010 ± 0.095 | 4.852 | 5.130 | 1.20 ± 0.03 |
