| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.152 ± 0.035 | 4.082 | 4.192 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 14.157 ± 0.091 | 14.034 | 14.322 | 3.41 ± 0.04 |
| `./target/release/lunacy nbody.bin` | 6.258 ± 0.031 | 6.224 | 6.308 | 1.51 ± 0.01 |
| `./target/unsafe/lunacy nbody.bin` | 5.718 ± 0.031 | 5.661 | 5.755 | 1.38 ± 0.01 |
