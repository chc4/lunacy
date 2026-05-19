| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.170 ± 0.016 | 4.133 | 4.185 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 13.102 ± 0.035 | 13.060 | 13.152 | 3.14 ± 0.01 |
| `./target/release/lunacy nbody.bin` | 5.629 ± 0.073 | 5.536 | 5.801 | 1.35 ± 0.02 |
| `./target/unsafe/lunacy nbody.bin` | 5.118 ± 0.068 | 5.008 | 5.189 | 1.23 ± 0.02 |
