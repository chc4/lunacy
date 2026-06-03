| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench 10` | 4.176 ± 0.033 | 4.090 | 4.199 | 1.06 ± 0.02 |
| `./target/interpreter/release/bench nbody.bin 10` | 11.441 ± 0.049 | 11.381 | 11.513 | 2.90 ± 0.04 |
| `./target/release/bench nbody.bin 10` | 4.456 ± 0.044 | 4.399 | 4.528 | 1.13 ± 0.02 |
| `./target/unsafe/bench nbody.bin 10` | 3.950 ± 0.052 | 3.894 | 4.077 | 1.00 |
