| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.171 ± 0.035 | 4.075 | 4.204 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 11.782 ± 0.048 | 11.706 | 11.851 | 2.82 ± 0.03 |
| `./target/release/lunacy nbody.bin` | 6.451 ± 0.060 | 6.374 | 6.555 | 1.55 ± 0.02 |
| `./target/unsafe/lunacy nbody.bin` | 5.938 ± 0.065 | 5.891 | 6.106 | 1.42 ± 0.02 |
