| Command | Mean [s] | Min [s] | Max [s] | Relative |
|:---|---:|---:|---:|---:|
| `lua5.1 bench.lua -- lua_benchmarking/benchmarks/nbody/bench 10` | 4.181 ± 0.065 | 4.122 | 4.358 | 1.07 ± 0.02 |
| `./target/interpreter/release/bench nbody.bin 10` | 10.935 ± 0.056 | 10.880 | 11.025 | 2.81 ± 0.02 |
| `./target/release/bench nbody.bin 10` | 4.232 ± 0.024 | 4.202 | 4.266 | 1.09 ± 0.01 |
| `./target/unsafe/bench nbody.bin 10` | 3.890 ± 0.027 | 3.852 | 3.943 | 1.00 |
