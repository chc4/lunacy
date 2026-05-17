| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.153 ± 0.029 | 4.102 | 4.189 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 13.551 ± 0.032 | 13.512 | 13.621 | 3.26 ± 0.02 |
| `./target/release/lunacy nbody.bin` | 6.188 ± 0.131 | 6.108 | 6.555 | 1.49 ± 0.03 |
| `./target/unsafe/lunacy nbody.bin` | 5.961 ± 0.118 | 5.845 | 6.263 | 1.44 ± 0.03 |
