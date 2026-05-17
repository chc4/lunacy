| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench` | 4.168 ± 0.027 | 4.105 | 4.186 | 1.00 |
| `./target/interpreter/release/lunacy nbody.bin` | 13.846 ± 0.087 | 13.778 | 14.013 | 3.32 ± 0.03 |
| `./target/release/lunacy nbody.bin` | 6.203 ± 0.017 | 6.175 | 6.232 | 1.49 ± 0.01 |
| `./target/unsafe/lunacy nbody.bin` | 5.977 ± 0.073 | 5.905 | 6.163 | 1.43 ± 0.02 |
