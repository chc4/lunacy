set shell := ["bash", "-c"]
TEST_FEATURES := "counters graph jit gas gc_sanitize"
# Runs hyperfine makes of each command before timing it, so the CPU has ramped
# up and caches are warm.
WARMUP := "3"
# The core hyperfine and the commands it times are pinned to (`taskset`), so a
# run never migrates onto a core that has not ramped up.
CPU := "2"

# Every test: `test`, then `test-stencils`.
tests: test test-stencils

# Run lunacy against the golden testcases
[env("RUST_BACKTRACE","1")]
test:
    # GC correctness tests
    cargo test "gc::" --features "gc_test,gc_sanitize" -- --test-threads 1
    # Normal interpreter tests
    cargo test --features "gc_sanitize"
    # Interpreter GC stress test
    cargo test --features "gc_stress gc_sanitize"
    # Golden suite with every block JIT compiled on first run (window ops run
    # through their interpreter path: `immediate_jit` copies no stencils)
    cargo test --features "immediate_jit gc_sanitize" --test golden_tests
    # Heap reset frees (no leak); needs the real finalizer, so runs without gc_sanitize
    cargo test --test gc_reset_frees

# Copy&patch window stencils (src/window.rs) as the JIT will use them: built
# with the `stencils` profile, optimized like release. The window unit
# tests also run in `just test` (debug); this runs them against optimized
# stencils, then the golden suite with `check_windows`: every window op the
# interpreter executes is also copy&patched and run natively, and the results
# must match. Then the golden suite with every block JIT compiled, optimized
# (`immediate_jit` copies no stencils, so window ops run through their
# interpreter path under the JIT's register allocation). (At opt-level 0,
# `NumericRR` keeps a jump table from the unfolded `match OP`, which the
# copier rejects: the check skips it and the JIT calls into the interpreter.)
STENCIL_OPT := "--profile stencils"
[env("RUST_BACKTRACE","1")]
test-stencils:
    cargo test --features check_windows --lib window:: {{STENCIL_OPT}}
    cargo test --features check_windows --test golden_tests {{STENCIL_OPT}}
    cargo test --features immediate_jit --test golden_tests {{STENCIL_OPT}}

# Runs of window residuals in a benchmark (docs/jit-register-cache.md): run it on
# the LBBV interpreter tier (every block entry counted, none hidden by the JIT)
# with the `graph` dump, then list each function's blocks with window runs,
# hottest first.
window-runs benchmark times='20':
    just _luac {{benchmark}}
    rm -f func_*.dot func_*.pdf
    cargo run --release --no-default-features --features "lbbv graph" --bin bench -- {{benchmark}}.bin {{times}}
    python3 tools/window_runs.py func_*.dot

# The JIT's window allocation for a benchmark, in window_dump.txt: each compiled
# block's entry window, then per residual its loads, stores and moves, what each
# jump transfers, and the window after it.
# With `ref`, revision `ref`'s (in target/compare/<ref>, as for `hyperfine-vs`)
# on this checkout's benchmark, in target/compare/<ref>/window_dump.txt.
window-dump benchmark times='20' ref='':
    #!/usr/bin/env bash
    set -euo pipefail
    just _luac {{benchmark}}
    if [ -z "{{ref}}" ]; then
        cargo run --release --features window_dump --bin bench -- {{benchmark}}.bin {{times}}
    else
        just _compare-worktree {{ref}}
        bin=$(realpath {{benchmark}}.bin)
        (cd target/compare/{{ref}} && cargo run --release --features window_dump --bin bench -- $bin {{times}})
    fi

# Save a benchmark's window dump as bench/window_dumps/<benchmark>.<name>.txt, a
# reference to compare window allocators against with `just window-dump-stats`.
window-dump-save benchmark name times='20':
    just window-dump {{benchmark}} {{times}}
    mkdir -p bench/window_dumps
    cp window_dump.txt bench/window_dumps/{{benchmark}}.{{name}}.txt

# A lua_tests program's window allocation under streaming allocation and each
# trace-building policy, as bench/window_dumps/<name>.<policy>.txt.
window-dump-policies name:
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    cargo build --release --features window_dump --bin lunacy
    mkdir -p bench/window_dumps
    for policy in streaming single unidirectional bidirectional; do LUNACY_TRACES=$policy ./target/release/lunacy {{name}}.bin > /dev/null && cp window_dump.txt bench/window_dumps/{{name}}.$policy.txt; done

# Executed loads, stores and moves of each benchmark, run `times` times, under
# streaming allocation and unidirectional traces, from their window dumps; a
# benchmark that fails (lunacy lacks some of Lua) says why.
window-dump-compare times +benchmarks:
    cargo build --release --features window_dump --bin bench
    for b in {{benchmarks}}; do just _luac $b || continue; for policy in streaming unidirectional; do if LUNACY_TRACES=$policy timeout 600 ./target/release/bench $b.bin {{times}} > /dev/null 2> target/window-dump-compare.err; then python3 tools/window_dump_stats.py --raw window_dump.txt | tail -1 | sed "s|^window_dump.txt|$b $policy|"; else echo "$b $policy: failed: $(grep -A1 -m1 panicked target/window-dump-compare.err | tail -1)"; fi; done; done

# The loads, stores and moves in window dumps, over all blocks and hot ones.
window-dump-stats *dumps='bench/window_dumps/*.txt':
    python3 tools/window_dump_stats.py {{dumps}}

[env("RUST_LOG", "debug")]
[env("RUST_BACKTRACE","1")]
test-debug:
    cargo test --features "gc_sanitize" -- --nocapture

watch:
    cargo watch -- cargo test

[env("RUST_LOG", "debug")]
debug name:
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    time cargo run --no-default-features --features "{{TEST_FEATURES}}" --bin lunacy -- {{name}}.bin

debug-jit name:
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    time cargo run --no-default-features --features "{{TEST_FEATURES}} immediate_jit" --bin lunacy -- {{name}}.bin

release name:
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    time cargo run --release --no-default-features --features "{{TEST_FEATURES}}" --bin lunacy -- {{name}}.bin

gdb-test name:
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    cargo build --release --bin lunacy
    gdb --args ./target/release/lunacy {{name}}.bin

# Benchmarks
# Compile a benchmark to <benchmark>.bin: this repository's
# benchmarks/<benchmark>, else lua_benchmarking's.
_luac benchmark:
    #!/usr/bin/env bash
    set -euo pipefail
    src=benchmarks/{{benchmark}}/bench.lua
    if [ ! -f $src ]; then src=lua_benchmarking/benchmarks/{{benchmark}}/bench.lua; fi
    luac5.1 -o {{benchmark}}.bin $src

run benchmark:
    just _luac {{benchmark}}
    time cargo run --release --bin bench -- {{benchmark}}.bin

[env("RUST_LOG", "debug")]
run-debug benchmark:
    just _luac {{benchmark}}
    time cargo run --bin bench -- {{benchmark}}.bin

graph name:
    luac5.1 -o {{name}}.bin {{name}}.lua
    cargo run --features graph --bin lunacy -- {{name}}.bin
graph-release name:
    luac5.1 -o {{name}}.bin {{name}}.lua
    cargo run --release --features graph --bin lunacy -- {{name}}.bin
# A benchmark's residual graphs with and without dynamic guards (feature
# `no_dynamic_guards`, Note [Dynamic guards]), in
# target/graphs/<benchmark>/{guards,no_guards}, and their blocks compared.
graph-guards benchmark times='10':
    #!/usr/bin/env bash
    set -euo pipefail
    just _luac {{benchmark}}
    for variant in guards no_guards; do
        features=graph
        if [ $variant = no_guards ]; then features="graph no_dynamic_guards"; fi
        cargo build --release --features "$features" --bin bench --target-dir target/graph-$variant
        dir=target/graphs/{{benchmark}}/$variant
        rm -rf $dir && mkdir -p $dir
        (cd $dir && ../../../graph-$variant/release/bench ../../../../{{benchmark}}.bin {{times}} > /dev/null)
    done
    tools/graph_blocks.py target/graphs/{{benchmark}}/guards target/graphs/{{benchmark}}/no_guards
# A benchmark's residual graphs at this checkout and at revision `ref` (built in
# target/compare/<ref>, as for `hyperfine-vs`), in
# target/graphs/<benchmark>/{current,<ref>}, and their blocks compared.
graph-vs ref benchmark times='10':
    #!/usr/bin/env bash
    set -euo pipefail
    just _luac {{benchmark}}
    cargo build --release --features graph --bin bench --target-dir target/graph-current
    just _compare-worktree {{ref}}
    (cd target/compare/{{ref}} && cargo build --release --features graph --bin bench --target-dir target/graph)
    bin=$(realpath {{benchmark}}.bin)
    for variant in current {{ref}}; do
        exe=$(realpath target/graph-current/release/bench)
        if [ $variant != current ]; then exe=$(realpath target/compare/{{ref}}/target/graph/release/bench); fi
        dir=target/graphs/{{benchmark}}/$variant
        rm -rf $dir && mkdir -p $dir
        (cd $dir && $exe $bin {{times}} > /dev/null)
    done
    tools/graph_blocks.py target/graphs/{{benchmark}}/current target/graphs/{{benchmark}}/{{ref}}
gdb name:
    luac5.1 -o {{name}}.bin {{name}}.lua
    cargo build --release --bin lunacy
    gdb --args ./target/release/lunacy {{name}}.bin


baseline benchmark:
    time lua5.1 bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench

gdb-benchmark benchmark:
    just _luac {{benchmark}}
    cargo build --release --bin bench
    gdb --args ./target/release/bench {{benchmark}}.bin

# Profile a benchmark: perf.data and flamegraph.svg here, or with `ref`, revision
# `ref`'s build (in target/compare/<ref>, as for `hyperfine-vs`) on this
# checkout's benchmark, its perf.data there and flamegraph-<ref>.svg here.
# `freq` is perf's sampling rate, in Hz.
flamegraph benchmark times='10' ref='' freq='997':
    #!/usr/bin/env bash
    set -euo pipefail
    just _luac {{benchmark}}
    rm -f /tmp/perf-*.map
    if [ -z "{{ref}}" ]; then
        cargo flamegraph -F {{freq}} --features "perf" --bin bench -- {{benchmark}}.bin {{times}}
        firefox -new-tab flamegraph.svg || true
    else
        dir=target/compare/{{ref}}
        just _compare-worktree {{ref}}
        bin=$(realpath {{benchmark}}.bin)
        svg=$(realpath .)/flamegraph-{{ref}}.svg
        (cd $dir && cargo flamegraph -F {{freq}} --features "perf" --bin bench -o $svg -- $bin {{times}})
    fi

benchmarks: (run "binarytrees") (run "life") (run "nbody")

# Interpreter
INTERPRETER_FEATURES := "magic"
interpreter-compile:
    cargo build --release --no-default-features --features "{{INTERPRETER_FEATURES}}" --bin bench --target-dir ./target/interpreter
interpreter benchmark: interpreter-compile
    just _luac {{benchmark}}
    time ./target/interpreter/release/bench {{benchmark}}.bin
interpreter-test name: interpreter-compile
    luac5.1 -o {{name}}.bin lua_tests/{{name}}.lua
    time ./target/interpreter/release/bench {{name}}.bin

# Unsafe
# Disassemble a window op's stencil at SKIP 0 as the `unsafe` profile builds it,
# in this checkout, or at revision `ref` (built in target/compare/<ref>, its
# submodules linked to this checkout's, as for `hyperfine-vs`). For example
# `just stencil-asm SetTableInteger`.
stencil-asm op ref='':
    #!/usr/bin/env bash
    set -euo pipefail
    dir=.
    if [ -n "{{ref}}" ]; then
        dir=target/compare/{{ref}}
        just _compare-worktree {{ref}}
    fi
    (cd $dir && cargo build --profile unsafe --no-default-features --features unsafe --bin bench -Z build-std="core,std,panic_abort")
    read start size < <(objdump -t -C $dir/target/unsafe/bench | awk '/{{op}}>::__stencil::<0>$/ {print $1, $5}')
    objdump -d -C --no-show-raw-insn --start-address=0x$start --stop-address=$((0x$start + 0x$size)) $dir/target/unsafe/bench | grep -E '^ +[0-9a-f]+:'

unsafe-compile:
    cargo build --profile unsafe --no-default-features --features unsafe --bin bench \
        -Z build-std="core,std,panic_abort"
unsafe benchmark: unsafe-compile
    just _luac {{benchmark}}
    time ./target/unsafe/bench {{benchmark}}.bin

gdb-unsafe benchmark: unsafe-compile
    just _luac {{benchmark}}
    gdb --args ./target/unsafe/bench {{benchmark}}.bin


# Hyperfine reports
# lunacy's interpreter, JIT and unsafe builds against Lua 5.1 and LuaJIT, its
# interpreter alone (-joff) and with its JIT. Lua 5.1 has no `bit`, so its run
# of a benchmark requiring it fails at once, and times nothing.
hyperfine benchmark times='10': unsafe-compile interpreter-compile
    just _luac {{benchmark}}
    cargo build --release --bin bench
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown hyperfine-{{benchmark}}-{{times}}.md \
        "lua5.1 bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench {{times}} || true" \
        "luajit -joff bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench {{times}}" \
        "luajit bench.lua -- lua_benchmarking/benchmarks/{{benchmark}}/bench {{times}}" \
        "./target/interpreter/release/bench {{benchmark}}.bin {{times}}" \
        "./target/release/bench {{benchmark}}.bin {{times}}" \
        "./target/unsafe/bench {{benchmark}}.bin {{times}}"
# Compare the trace-building policies of the window allocator, and streaming
# allocation, on a benchmark
# (LUNACY_TRACES; see docs/trace-register-allocation.md).
hyperfine-traces benchmark times='10' policies='streaming,single,unidirectional,bidirectional':
    just _luac {{benchmark}}
    cargo build --release --bin bench
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown hyperfine-{{benchmark}}-{{times}}-traces.md -L policy {{policies}} \
        "LUNACY_TRACES={policy} ./target/release/bench {{benchmark}}.bin {{times}}"
# `hyperfine-traces` over the benchmarks lunacy runs, each run enough times for
# a stable mean. life runs twice: the difference between its 1000 and 5000 runs
# is the steady-state cost of the code, the rest the upfront cost (compiling).
hyperfines-traces policies='streaming,unidirectional,bidirectional': (hyperfine-traces "life" "1000" policies) (hyperfine-traces "life" "5000" policies) (hyperfine-traces "nbody" "10" policies) (hyperfine-traces "queens" "3000" policies) (hyperfine-traces "fannkuch_redux" "150" policies)

# mimalloc's statistics for a benchmark under each trace policy, before and
# after the heap's final reset (feature `alloc_stats`), each policy's in
# target/alloc-stats-<benchmark>-<policy>.txt.
alloc-stats benchmark times='10' policies='streaming unidirectional':
    just _luac {{benchmark}}
    cargo build --release --features alloc_stats --bin bench
    for policy in {{policies}}; do LUNACY_TRACES=$policy ./target/release/bench {{benchmark}}.bin {{times}} > /dev/null 2> target/alloc-stats-{{benchmark}}-$policy.txt; echo "target/alloc-stats-{{benchmark}}-$policy.txt"; done

# Revision `ref` checked out in a detached worktree, target/compare/<ref>, kept
# for reruns, its submodules linked to this checkout's.
_compare-worktree ref:
    #!/usr/bin/env bash
    set -euo pipefail
    dir=target/compare/{{ref}}
    test -d $dir || git worktree add --detach $dir {{ref}}
    git -C $dir checkout --detach {{ref}}
    for module in dynasm-rs memmap2-rs; do test -L $dir/$module || { rmdir $dir/$module && ln -s "$(realpath $module)" $dir/$module; }; done

# Compare this checkout's release build against revision `ref`'s on one
# benchmark: `ref` is built in a detached worktree under target/compare/ (kept
# for reruns, its submodules linked to this checkout's).
hyperfine-vs ref benchmark times='10':
    just _luac {{benchmark}}
    cargo build --release --bin bench
    just _compare-worktree {{ref}}
    cd target/compare/{{ref}} && cargo build --release --bin bench
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown hyperfine-{{benchmark}}-vs-{{ref}}.md \
        "target/compare/{{ref}}/target/release/bench {{benchmark}}.bin {{times}}" \
        "./target/release/bench {{benchmark}}.bin {{times}}"
# Compare this checkout's release build with and without cargo feature
# `feature` on one benchmark: the feature's build is in target/features/<feature>.
hyperfine-feature feature benchmark times='10':
    just _luac {{benchmark}}
    cargo build --release --bin bench
    cargo build --release --features {{feature}} --bin bench --target-dir target/features/{{feature}}
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown hyperfine-{{benchmark}}-{{times}}-{{feature}}.md \
        -n default "./target/release/bench {{benchmark}}.bin {{times}}" \
        -n {{feature}} "target/features/{{feature}}/release/bench {{benchmark}}.bin {{times}}"
hyperfine-jit benchmark:
    just _luac {{benchmark}}
    cargo build --release --bin bench
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown hyperfine-{{benchmark}}-jit.md \
        "./target/release/bench {{benchmark}}.bin"
hyperfine-unsafe benchmark: unsafe-compile
    just _luac {{benchmark}}
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown hyperfine-{{benchmark}}-unsafe.md \
        "./target/unsafe/bench {{benchmark}}.bin"


# `hyperfine` over the benchmarks lunacy runs, each run enough times for a
# stable mean; life twice, as for `hyperfines-traces`. euler14's count is the
# bound of its search.
hyperfines: (hyperfine "life" "1000") (hyperfine "life" "5000") (hyperfine "nbody" "10") (hyperfine "queens" "3000") (hyperfine "fannkuch_redux" "150") (hyperfine "euler14" "1000000") (hyperfine "nsieve_bit" "10")

all: test benchmarks (hyperfine "binarytrees")
