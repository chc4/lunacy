| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.141 ± 0.028 | 4.093 | 4.173 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 13.725 ± 0.073 | 13.647 | 13.862 | 3.31 ± 0.03 |
| `./target/release/lunacy nbody.bin` | 5.973 ± 0.062 | 5.881 | 6.065 | 1.44 ± 0.02 |
| `./target/unsafe/lunacy nbody.bin` | 5.712 ± 0.068 | 5.595 | 5.801 | 1.38 ± 0.02 |
