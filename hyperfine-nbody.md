| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench 10` | 4.293 ± 0.080 | 4.156 | 4.369 | 1.12 ± 0.03 |
| `./target/interpreter/release/bench nbody.bin 10` | 4.592 ± 0.098 | 4.429 | 4.791 | 1.20 ± 0.04 |
| `./target/release/bench nbody.bin 10` | 4.130 ± 0.161 | 4.005 | 4.562 | 1.08 ± 0.05 |
| `./target/unsafe/bench nbody.bin 10` | 3.837 ± 0.087 | 3.692 | 3.953 | 1.00 |
