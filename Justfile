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
# in release, so the stencils checked are the ones the JIT copies (a build
# with any other optimization, codegen units or LTO compiles them to different
# code: `tools/stencil_diff.py` compares two builds'). The window unit
# tests also run in `just test` (debug); this runs them against optimized
# stencils, then the golden suite with `check_windows`: every window op the
# interpreter executes is also copy&patched and run natively, and the results
# must match. Then the golden suite with every block JIT compiled, optimized
# (`immediate_jit` copies no stencils, so window ops run through their
# interpreter path under the JIT's register allocation). (At opt-level 0,
# `NumericRR` keeps a jump table from the unfolded `match OP`, which the
# copier rejects: the check skips it and the JIT calls into the interpreter.)
STENCIL_OPT := "--release"
[env("RUST_BACKTRACE","1")]
test-stencils:
    cargo test --features check_windows --lib window:: {{STENCIL_OPT}}
    cargo test --features check_windows --test golden_tests {{STENCIL_OPT}}
    cargo test --features immediate_jit --test golden_tests {{STENCIL_OPT}}

# A benchmark's run traced (feature `tracing`) to working/lunacy.fxt, a
# Perfetto trace (https://ui.perfetto.dev opens it), and summarized with
# Perfetto's trace processor: its JIT compiles, and its bailouts by reason and
# by where they are. Built as the benchmarks are timed: the unsafe profile.
trace benchmark times='10' features='unsafe':
    just _luac {{benchmark}}
    cargo build --profile unsafe --no-default-features --features "{{features}} tracing" --bin bench \
        --target-dir target/tracing -Z build-std="core,std,panic_abort"
    cd working && ../target/tracing/unsafe/bench {{benchmark}}.bin {{times}} > /dev/null
    python3 tools/perfetto_summary.py working/lunacy.fxt

# `trace`'s summary of working/lunacy.fxt again.
show-trace:
    python3 tools/perfetto_summary.py working/lunacy.fxt

# SQL against `trace`'s working/lunacy.fxt (tools/trace_sql.py): the
# specializer's version choices, compiled versions and blocks are the views
# spec_version, spec_block and block_summary.
trace-sql query:
    python3 tools/trace_sql.py "{{query}}"

# Golden tests, each against its expected output, under the default build,
# immediate_jit, no_dynamic_guards and both (tools/golden_builds.py).
golden-builds +tests:
    python3 tools/golden_builds.py {{tests}}

# Runs of window residuals in a benchmark (docs/jit-register-cache.md): run it on
# the LBBV interpreter tier (every block entry counted, none hidden by the JIT)
# with the `graph` dump (working/func_*.dot), then list each function's blocks
# with window runs, hottest first.
window-runs benchmark times='20':
    just _luac {{benchmark}}
    rm -f working/func_*.dot working/func_*.pdf
    cd working && cargo run --release --no-default-features --features graph --bin bench -- {{benchmark}}.bin {{times}}
    python3 tools/window_runs.py working/func_*.dot

# The JIT's window allocation for a benchmark, in working/window_dump.txt: each compiled
# block's entry window, then per residual its loads, stores and moves, what each
# jump transfers, and the window after it.
# With `ref`, revision `ref`'s (in target/compare/<ref>, as for `hyperfine-vs`)
# on this checkout's benchmark, in target/compare/<ref>/window_dump.txt.
# The allocator code a benchmark's run executed most, from its window dump
# (tools/window_hot.py): `args` as the tool takes them (`--blocks`, `--top N`).
window-hot benchmark times='20' *args: (window-dump benchmark times)
    python3 tools/window_hot.py working/window_dump.txt {{args}}

window-dump benchmark times='20' ref='':
    #!/usr/bin/env bash
    set -euo pipefail
    just _luac {{benchmark}}
    if [ -z "{{ref}}" ]; then
        cd working && cargo run --release --features window_dump --bin bench -- {{benchmark}}.bin {{times}}
    else
        just _compare-worktree {{ref}}
        bin=$(realpath working/{{benchmark}}.bin)
        (cd target/compare/{{ref}} && cargo run --release --features window_dump --bin bench -- $bin {{times}})
    fi

# The size of each window op's stencil a benchmark's JIT code copies, in the
# release build and the unsafe one, as the copier reports them (feature
# `jit_disasm`): the body it splats (bytes and instructions) and the stencil
# function it copied it from, in working/stencil_sizes-release.txt and
# working/stencil_sizes-unsafe.txt.
stencil-sizes benchmark='queens' times='10':
    just _luac {{benchmark}}
    cd working && cargo run --release --features jit_disasm --bin bench --target-dir ../target/jit_disasm \
        -- {{benchmark}}.bin {{times}} > /dev/null
    mv working/stencil_sizes.txt working/stencil_sizes-release.txt
    cd working && cargo run --profile unsafe --no-default-features --features "unsafe jit_disasm" --bin bench \
        --target-dir ../target/jit_disasm -Z build-std="core,std,panic_abort" -- {{benchmark}}.bin {{times}} > /dev/null
    mv working/stencil_sizes.txt working/stencil_sizes-unsafe.txt
    head -25 working/stencil_sizes-unsafe.txt

# Cold code in every window op's stencil (see tools/stencil_cold.py), in the
# release and unsafe builds, and every stencil's assembly in
# working/stencils-release.s and working/stencils-unsafe.s.
stencil-cold: unsafe-compile
    cargo build --release --bin bench
    cargo build --release --features jit_disasm --bin demangle --target-dir target/jit_disasm
    mkdir -p working
    python3 tools/stencil_cold.py target/release/bench --dump working/stencils-release.s
    python3 tools/stencil_cold.py target/unsafe/bench --dump working/stencils-unsafe.s

# A benchmark's JIT code, disassembled when the VM drops it and annotated with
# what emitted it (regions, blocks, residuals, thunk stubs, the blocks and
# helpers branches go to), in working/jit_disasm.txt. Built as `unsafe-compile`
# builds, with `features` (by default the unsafe build's).
jit-disasm benchmark times='10' features='unsafe':
    just _luac {{benchmark}}
    cd working && cargo run --profile unsafe --no-default-features --features "{{features}} jit_disasm" --bin bench \
        --target-dir ../target/jit_disasm -Z build-std="core,std,panic_abort" -- {{benchmark}}.bin {{times}} > /dev/null
    @echo working/jit_disasm.txt

# Where a benchmark's JIT code goes, in bytes (tools/jit_code_size.py): by
# function, by kind of residual, and the largest blocks, from its annotated
# disassembly (`jit-disasm`).
jit-code-size benchmark times='10': (jit-disasm benchmark times)
    python3 tools/jit_code_size.py working/jit_disasm.txt

# How much machine code LuaJIT's JIT generates for a benchmark
# (tools/luajit_mcode.lua), to compare with `jit-code-size`.
luajit-mcode benchmark times='10':
    just _luajitc {{benchmark}}
    luajit tools/luajit_mcode.lua working/{{benchmark}}.luajit.bin {{times}}

# Profile a benchmark with IBS (AMD's precise sampling: a sample is the
# instruction that ran, with no skid), every `period` cycles, built as
# `jit-disasm` builds with the perf map too, and join the samples on the JIT's
# code to its disassembly (tools/jit_samples.py): by what emitted the code, and,
# with `op` (a disassembly note, like `PushFrame`), that code's instructions
# summed over its copies. working/jit-profile.data, and the sampled
# disassembly with counts in working/jit_samples.txt.
jit-profile benchmark times='10' op='' period='20000' features='unsafe':
    just _luac {{benchmark}}
    cargo build --profile unsafe --no-default-features --features "{{features}} perf jit_disasm" --bin bench \
        --target-dir target/jit_disasm -Z build-std="core,std,panic_abort"
    cd working && perf record -e ibs_op// -c {{period}} -o jit-profile.data ../target/jit_disasm/unsafe/bench {{benchmark}}.bin {{times}} > /dev/null
    cd working && perf script -i jit-profile.data -F ip,sym > jit-profile.samples
    python3 tools/jit_samples.py working/jit_disasm.txt working/jit-profile.samples --out working/jit_samples.txt {{ if op != "" { "--op '" + op + "'" } else { "" } }}

# Save a benchmark's window dump as bench/window_dumps/<benchmark>.<name>.txt, a
# reference to compare window allocators against with `just window-dump-stats`.
window-dump-save benchmark name times='20':
    just window-dump {{benchmark}} {{times}}
    mkdir -p bench/window_dumps
    cp working/window_dump.txt bench/window_dumps/{{benchmark}}.{{name}}.txt

# A lua_tests program's window allocation under streaming allocation and each
# trace-building policy, as bench/window_dumps/<name>.<policy>.txt.
window-dump-policies name: (_luac-test name)
    cargo build --release --features window_dump --bin lunacy
    mkdir -p bench/window_dumps
    for policy in streaming single unidirectional bidirectional; do (cd working && LUNACY_TRACES=$policy ../target/release/lunacy {{name}}.bin > /dev/null) && cp working/window_dump.txt bench/window_dumps/{{name}}.$policy.txt; done

# Executed loads, stores and moves of each benchmark, run `times` times, under
# streaming allocation and unidirectional traces, from their window dumps; a
# benchmark that fails (lunacy lacks some of Lua) says why.
window-dump-compare times +benchmarks:
    cargo build --release --features window_dump --bin bench
    for b in {{benchmarks}}; do just _luac $b || continue; for policy in streaming unidirectional; do if (cd working && LUNACY_TRACES=$policy timeout 600 ../target/release/bench $b.bin {{times}} > /dev/null 2> ../target/window-dump-compare.err); then python3 tools/window_dump_stats.py --raw working/window_dump.txt | tail -1 | sed "s|^working/window_dump.txt|$b $policy|"; else echo "$b $policy: failed: $(grep -A1 -m1 panicked target/window-dump-compare.err | tail -1)"; fi; done; done

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
debug name: (_luac-test name)
    cd working && time cargo run --no-default-features --features "{{TEST_FEATURES}}" --bin lunacy -- {{name}}.bin

debug-jit name: (_luac-test name)
    cd working && time cargo run --no-default-features --features "{{TEST_FEATURES}} immediate_jit" --bin lunacy -- {{name}}.bin

release name: (_luac-test name)
    cd working && time cargo run --release --no-default-features --features "{{TEST_FEATURES}}" --bin lunacy -- {{name}}.bin

gdb-test name: (_luac-test name)
    cargo build --release --bin lunacy
    gdb --args ./target/release/lunacy working/{{name}}.bin

# Compile lua_tests/<name>.lua to working/<name>.bin.
_luac-test name:
    mkdir -p working
    luac5.1 -o working/{{name}}.bin lua_tests/{{name}}.lua

# Benchmarks
# Compile a benchmark to working/<benchmark>.bin: this repository's
# benchmarks/<benchmark>, else lua_benchmarking's, bundled with its modules and
# benchmarks/prelude.lua (`tools/bundle_bench.py`) in working/<benchmark>.lua.
_luac benchmark:
    mkdir -p working
    python3 tools/bundle_bench.py {{benchmark}} > working/{{benchmark}}.lua
    luac5.1 -o working/{{benchmark}}.bin working/{{benchmark}}.lua

# Compile a benchmark, as `_luac`, to LuaJIT's bytecode in
# working/<benchmark>.luajit.bin: LuaJIT can't load luac5.1's.
_luajitc benchmark:
    mkdir -p working
    python3 tools/bundle_bench.py {{benchmark}} > working/{{benchmark}}.luajit.lua
    luajit -b working/{{benchmark}}.luajit.lua working/{{benchmark}}.luajit.bin

# Compile a benchmark, as `_luac`, to Lua 5.5's bytecode in
# working/<benchmark>.lua55.bin.
_lua55c benchmark:
    mkdir -p working
    python3 tools/bundle_bench.py {{benchmark}} > working/{{benchmark}}.lua55.lua
    luac5.5 -o working/{{benchmark}}.lua55.bin working/{{benchmark}}.lua55.lua

# Luau's copy of a benchmark, as `_luac`, in working/<benchmark>.luau: its
# bundle, then a call of its `run_iter` with the count Luau is given (`-a`).
# Luau has no dofile, and runs each file with its own globals, so it can't run
# the benchmark as bench.lua does for the other Luas.
_luauc benchmark:
    #!/usr/bin/env bash
    set -euo pipefail
    mkdir -p working
    { python3 tools/bundle_bench.py {{benchmark}}; printf '\nrun_iter(tonumber((...)))\n'; } > working/{{benchmark}}.luau

run benchmark:
    just _luac {{benchmark}}
    time cargo run --release --bin bench -- working/{{benchmark}}.bin

[env("RUST_LOG", "debug")]
run-debug benchmark:
    just _luac {{benchmark}}
    time cargo run --bin bench -- working/{{benchmark}}.bin

# <name>.lua's residual graphs, as working/func_<line>.dot and .pdf.
graph name:
    mkdir -p working
    luac5.1 -o working/{{name}}.bin {{name}}.lua
    cd working && cargo run --features graph --bin lunacy -- {{name}}.bin
graph-release name:
    mkdir -p working
    luac5.1 -o working/{{name}}.bin {{name}}.lua
    cd working && cargo run --release --features graph --bin lunacy -- {{name}}.bin
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
        (cd $dir && ../../../graph-$variant/release/bench ../../../../working/{{benchmark}}.bin {{times}} > /dev/null)
    done
    tools/graph_blocks.py target/graphs/{{benchmark}}/guards target/graphs/{{benchmark}}/no_guards
# `graph-guards` over HYPERFINES: a benchmark whose run fails under
# `no_dynamic_guards` says so.
graphs-guards:
    #!/usr/bin/env bash
    set -uo pipefail
    for run in {{HYPERFINES}}; do echo "== ${run%:*} ${run#*:}"; just graph-guards ${run%:*} ${run#*:} 2>&1 | grep -E 'panicked|jump in| \| ' | tail -n 3; done
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
    bin=$(realpath working/{{benchmark}}.bin)
    for variant in current {{ref}}; do
        exe=$(realpath target/graph-current/release/bench)
        if [ $variant != current ]; then exe=$(realpath target/compare/{{ref}}/target/graph/release/bench); fi
        dir=target/graphs/{{benchmark}}/$variant
        rm -rf $dir && mkdir -p $dir
        (cd $dir && $exe $bin {{times}} > /dev/null)
    done
    tools/graph_blocks.py target/graphs/{{benchmark}}/current target/graphs/{{benchmark}}/{{ref}}

# `graph-vs ref` over HYPERFINES.
graphs-vs ref:
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{HYPERFINES}}; do echo "== ${run%:*} ${run#*:}"; just graph-vs {{ref}} ${run%:*} ${run#*:} 2>/dev/null | sed -n '/ \/ /,$p'; done
gdb name:
    mkdir -p working
    luac5.1 -o working/{{name}}.bin {{name}}.lua
    cargo build --release --bin lunacy
    gdb --args ./target/release/lunacy working/{{name}}.bin


baseline benchmark times='10':
    just _luac {{benchmark}}
    time lua5.1 bench.lua -- working/{{benchmark}}.bin {{times}}

gdb-benchmark benchmark:
    just _luac {{benchmark}}
    cargo build --release --bin bench
    gdb --args ./target/release/bench working/{{benchmark}}.bin

# Profile a benchmark, built with the `flamegraph` profile (the unsafe build with
# frame pointers) and unwound through frame pointers, as perf's default DWARF
# unwinding can't unwind JIT code, which has no unwind tables (`tools/unwound.py`
# reports how much of a profile reached `main`): perf.data and flamegraph.svg in
# working/, or with `ref`, revision `ref`'s build (in target/compare/<ref>, as
# for `hyperfine-vs`; it must have the profile) on this checkout's benchmark,
# its perf.data there and working/flamegraph-<ref>.svg.
# `freq` is perf's sampling rate, in Hz; `features` the build's (`magic perf`
# for the interpreter alone, without the JIT).
flamegraph benchmark times='10' ref='' freq='997' features='unsafe perf':
    #!/usr/bin/env bash
    set -euo pipefail
    just _luac {{benchmark}}
    # The profile's panic strategy needs std rebuilt, as for `unsafe-compile`:
    # `-Z build-std`, which `cargo flamegraph` takes from the environment.
    export CARGO_UNSTABLE_BUILD_STD=core,std,panic_abort
    if [ -z "{{ref}}" ]; then
        (cd working && cargo flamegraph -c "record -F {{freq}} --call-graph fp -g" --profile flamegraph --no-default-features --features "{{features}}" --bin bench -- {{benchmark}}.bin {{times}})
        firefox -new-tab working/flamegraph.svg || true
    else
        dir=target/compare/{{ref}}
        just _compare-worktree {{ref}}
        bin=$(realpath working/{{benchmark}}.bin)
        svg=$(realpath working)/flamegraph-{{ref}}.svg
        (cd $dir && cargo flamegraph -c "record -F {{freq}} --call-graph fp -g" --profile flamegraph --no-default-features --features "{{features}}" --bin bench -o $svg -- $bin {{times}})
    fi

# `flamegraph` of revision `ref` (as for `hyperfine-vs`) and of this checkout on
# one benchmark, kept side by side in working/: flamegraph-<benchmark>-<ref>.svg
# and perf-<benchmark>-<ref>.data, flamegraph-<benchmark>.svg and
# perf-<benchmark>.data, and each one's hottest symbols. The runs' JIT symbol
# maps (/tmp/perf-<pid>.map) are kept, as every profile's are, so any perf.data
# reports afterwards: a run's map replaces a stale one of its pid.
flamegraph-vs ref benchmark times='10' freq='997' top='25':
    #!/usr/bin/env bash
    set -euo pipefail
    just _luac {{benchmark}}
    export CARGO_UNSTABLE_BUILD_STD=core,std,panic_abort
    here=$(realpath working)
    bin=$(realpath working/{{benchmark}}.bin)
    dir=target/compare/{{ref}}
    just _compare-worktree {{ref}}
    (cd $dir && cargo flamegraph -c "record -F {{freq}} --call-graph fp -g" --profile flamegraph --no-default-features --features "unsafe perf" --bin bench -o $here/flamegraph-{{benchmark}}-{{ref}}.svg -- $bin {{times}})
    mv $dir/perf.data working/perf-{{benchmark}}-{{ref}}.data
    (cd working && cargo flamegraph -c "record -F {{freq}} --call-graph fp -g" --profile flamegraph --no-default-features --features "unsafe perf" --bin bench -o flamegraph-{{benchmark}}.svg -- {{benchmark}}.bin {{times}})
    mv working/perf.data working/perf-{{benchmark}}.data
    # `head` closing the pipe early isn't a failure.
    set +o pipefail
    for data in working/perf-{{benchmark}}-{{ref}}.data working/perf-{{benchmark}}.data; do
        echo "== $data"
        perf report -i $data --no-children -g none --sort sym --stdio 2>/dev/null | grep '%' | head -n {{top}}
    done

# `flamegraph` over HYPERFINES, sampling at `freq` Hz: for each run,
# working/perf-<benchmark>-<times>.data and flamegraph-<benchmark>-<times>.svg,
# then each profile's share of time by tier (tools/tiers.py): JIT code, the
# interpreter, compiling, and GC. perf runs the benchmark itself: under
# `cargo flamegraph`, samples from the run's start are the pre-exec process's,
# which perf can't resolve.
flamegraphs freq='19997':
    #!/usr/bin/env bash
    set -euo pipefail
    cargo build --profile flamegraph --no-default-features --features "unsafe perf" --bin bench -Z build-std="core,std,panic_abort"
    profiles=()
    for run in {{HYPERFINES}}; do
        benchmark=${run%:*}; times=${run#*:}
        just _luac $benchmark
        (cd working && perf record -F {{freq}} --call-graph fp -g -o perf-$benchmark-$times.data -- ../target/flamegraph/bench $benchmark.bin $times > /dev/null)
        flamegraph --perfdata working/perf-$benchmark-$times.data -o working/flamegraph-$benchmark-$times.svg > /dev/null
        profiles+=(working/perf-$benchmark-$times.data)
    done
    python3 tools/tiers.py "${profiles[@]}"

benchmarks: (run "binarytrees") (run "life") (run "nbody")

# Interpreter: no JIT, every closure run by the specializer's interpreter loop.
INTERPRETER_FEATURES := "magic"
interpreter-compile:
    cargo build --release --no-default-features --features "{{INTERPRETER_FEATURES}}" --bin bench --bin lunacy --target-dir ./target/interpreter
interpreter benchmark: interpreter-compile
    just _luac {{benchmark}}
    time ./target/interpreter/release/bench working/{{benchmark}}.bin
interpreter-test name: interpreter-compile (_luac-test name)
    time ./target/interpreter/release/lunacy working/{{name}}.bin

# Unsafe
# Disassemble a window op's stencil at SKIP 0 as the `unsafe` profile builds it,
# in this checkout, or at revision `ref` (built in target/compare/<ref>, its
# submodules linked to this checkout's, as for `hyperfine-vs`). For example
# `just stencil-asm SetTableInteger`, or with its const params as its demangled
# symbol names them, `just stencil-asm 'PopFrame<false,
# {lunacy::specialize::Count::Many}, {lunacy::specialize::Count::Many}>'`.
stencil-asm op ref='':
    #!/usr/bin/env bash
    set -euo pipefail
    dir=.
    if [ -n "{{ref}}" ]; then
        dir=target/compare/{{ref}}
        just _compare-worktree {{ref}}
    fi
    (cd $dir && cargo build --profile unsafe --no-default-features --features unsafe --bin bench -Z build-std="core,std,panic_abort")
    # Demangled by the `demangle` bin: objdump's -C leaves v0 symbols with enum
    # const generics mangled.
    cargo build --release --features jit_disasm --bin demangle --target-dir target/jit_disasm
    demangle=target/jit_disasm/release/demangle
    read start size < <(objdump -t $dir/target/unsafe/bench | $demangle | awk -v op='{{op}}>::__stencil::<0>' 'substr($0, length($0) - length(op) + 1) == op {print $1, $5}')
    objdump -d --no-show-raw-insn --start-address=0x$start --stop-address=$((0x$start + 0x$size)) $dir/target/unsafe/bench | $demangle | grep -E '^ +[0-9a-f]+:'

unsafe-compile:
    cargo build --profile unsafe --no-default-features --features unsafe --bin bench \
        -Z build-std="core,std,panic_abort"
unsafe benchmark: unsafe-compile
    just _luac {{benchmark}}
    time ./target/unsafe/bench working/{{benchmark}}.bin

gdb-unsafe benchmark: unsafe-compile
    just _luac {{benchmark}}
    gdb --args ./target/unsafe/bench working/{{benchmark}}.bin


# Hyperfine reports
# lunacy's release and unsafe builds against LuaJIT, its interpreter alone
# (-joff) and with its JIT, into the benchmark history (tools/bench_history.py).
hyperfine benchmark times='10': unsafe-compile
    just _luac {{benchmark}}
    just _luajitc {{benchmark}}
    cargo build --release --bin bench
    # A build whose run fails (e.g. past the JIT buffer's end) is still timed,
    # and left out of the history for its exit code.
    taskset -c {{CPU}} hyperfine -i --warmup {{WARMUP}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}.md \
        --export-json working/hyperfine-{{benchmark}}-{{times}}.json \
        -n "luajit -joff" "luajit -joff bench.lua -- working/{{benchmark}}.luajit.bin {{times}}" \
        -n luajit "luajit bench.lua -- working/{{benchmark}}.luajit.bin {{times}}" \
        -n release "./target/release/bench working/{{benchmark}}.bin {{times}}" \
        -n unsafe "./target/unsafe/bench working/{{benchmark}}.bin {{times}}"
    python3 tools/bench_history.py record working/hyperfine-{{benchmark}}-{{times}}.json --benchmark {{benchmark}} --arg {{times}}

# `hyperfine`, with lunacy's interpreter (no JIT), Lua 5.1, Lua 5.5, and Luau
# interpreted and with its native code generator too. Lua 5.1 and 5.5's and the
# interpreter's runs take most of its time. None of the others has `bit`, so
# their runs of a benchmark requiring it fail at once, and time nothing.
hyperfine-full benchmark times='10': unsafe-compile interpreter-compile
    just _luac {{benchmark}}
    just _luajitc {{benchmark}}
    just _lua55c {{benchmark}}
    just _luauc {{benchmark}}
    cargo build --release --bin bench
    # A command failing (lua5.1, lua5.5 and Luau lack the bit library) is timed,
    # and left out of the history for its exit code.
    taskset -c {{CPU}} hyperfine -i --warmup {{WARMUP}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}.md \
        --export-json working/hyperfine-{{benchmark}}-{{times}}.json \
        -n lua5.1 "lua5.1 bench.lua -- working/{{benchmark}}.bin {{times}}" \
        -n lua5.5 "lua5.5 bench.lua -- working/{{benchmark}}.lua55.bin {{times}}" \
        -n luau "luau -O2 working/{{benchmark}}.luau -a {{times}}" \
        -n "luau --codegen" "luau -O2 --codegen working/{{benchmark}}.luau -a {{times}}" \
        -n "luajit -joff" "luajit -joff bench.lua -- working/{{benchmark}}.luajit.bin {{times}}" \
        -n luajit "luajit bench.lua -- working/{{benchmark}}.luajit.bin {{times}}" \
        -n interpreter "./target/interpreter/release/bench working/{{benchmark}}.bin {{times}}" \
        -n release "./target/release/bench working/{{benchmark}}.bin {{times}}" \
        -n unsafe "./target/unsafe/bench working/{{benchmark}}.bin {{times}}"
    python3 tools/bench_history.py record working/hyperfine-{{benchmark}}-{{times}}.json --benchmark {{benchmark}} --arg {{times}}
# Compare the trace-building policies of the window allocator, and streaming
# allocation, on a benchmark
# (LUNACY_TRACES; see docs/trace-register-allocation.md).
hyperfine-traces benchmark times='10' policies='streaming,single,unidirectional,bidirectional':
    just _luac {{benchmark}}
    cargo build --release --bin bench
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}-traces.md -L policy {{policies}} \
        "LUNACY_TRACES={policy} ./target/release/bench working/{{benchmark}}.bin {{times}}"
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
    for policy in {{policies}}; do LUNACY_TRACES=$policy ./target/release/bench working/{{benchmark}}.bin {{times}} > /dev/null 2> target/alloc-stats-{{benchmark}}-$policy.txt; echo "target/alloc-stats-{{benchmark}}-$policy.txt"; done

# Revision `ref` checked out in a detached worktree, target/compare/<ref>, kept
# for reruns, its submodules linked to this checkout's.
_compare-worktree ref:
    #!/usr/bin/env bash
    set -euo pipefail
    dir=target/compare/{{ref}}
    # Resolved here: in the worktree, a relative ref (HEAD, HEAD~1) names the
    # worktree's own commit.
    rev=$(git rev-parse {{ref}})
    test -d $dir || git worktree add --detach $dir $rev
    git -C $dir checkout --detach $rev
    for module in dynasm-rs memmap2-rs lua_benchmarking; do test -L $dir/$module || { rmdir $dir/$module && ln -s "$(realpath $module)" $dir/$module; }; done

# This checkout's release and unsafe builds (as `unsafe-compile` builds), and
# revision `ref`'s, in a detached worktree under target/compare/ (kept for
# reruns, its submodules linked to this checkout's).
_build-vs ref:
    cargo build --release --bin bench
    just unsafe-compile
    just _compare-worktree {{ref}}
    cd target/compare/{{ref}} && cargo build --release --bin bench && just unsafe-compile

# Compare this checkout's release and unsafe builds against revision `ref`'s on
# one benchmark (built as `_build-vs` builds them).
hyperfine-vs ref benchmark times='10': (_build-vs ref)
    just _luac {{benchmark}}
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}-vs-{{ref}}.md \
        --export-json working/hyperfine-{{benchmark}}-{{times}}-vs-{{ref}}.json \
        -n "ref release" "target/compare/{{ref}}/target/release/bench working/{{benchmark}}.bin {{times}}" \
        -n release "./target/release/bench working/{{benchmark}}.bin {{times}}" \
        -n "ref unsafe" "target/compare/{{ref}}/target/unsafe/bench working/{{benchmark}}.bin {{times}}" \
        -n unsafe "./target/unsafe/bench working/{{benchmark}}.bin {{times}}"
    python3 tools/bench_history.py record working/hyperfine-{{benchmark}}-{{times}}-vs-{{ref}}.json --benchmark {{benchmark}} --arg {{times}} --ref {{ref}}

# Revision `ref`'s release and unsafe builds (as `_build-vs` builds them) on
# every benchmark of HYPERFINES, into the history (tools/bench_history.py): to
# fill in the commits before the history was kept.
bench-rev ref:
    #!/usr/bin/env bash
    set -euo pipefail
    just _compare-worktree {{ref}}
    (cd target/compare/{{ref}} && cargo build --release --bin bench && just unsafe-compile)
    for run in {{HYPERFINES}}; do
        benchmark=${run%:*}; times=${run#*:}
        just _luac $benchmark
        taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-json working/hyperfine-$benchmark-$times-{{ref}}.json \
            -n "ref release" "target/compare/{{ref}}/target/release/bench working/$benchmark.bin $times" \
            -n "ref unsafe" "target/compare/{{ref}}/target/unsafe/bench working/$benchmark.bin $times"
        python3 tools/bench_history.py record working/hyperfine-$benchmark-$times-{{ref}}.json --benchmark $benchmark --arg $times --ref {{ref}}
    done

# The benchmark history (tools/bench_history.py): each benchmark's and build's
# latest, dirty, best and first times, regressions flagged, and the charts, in
# working/history.html.
bench-history:
    python3 tools/bench_history.py report
    python3 tools/bench_history.py plot

# The latest commit's times from the benchmark history as a grouped bar chart,
# a group per benchmark, in rows of `per_row` each on its own scale, in
# working/bars.html (tools/bench_bars.py): `builds`, the implementations, in bar
# order, and `clamp`, those whose bars don't set a row's scale past 1.5 times
# the rest's highest (comma separated).
bench-bars builds='lua5.1,lua5.5,luau,luau --codegen,luajit -joff,luajit,interpreter,release,unsafe' clamp='lua5.1,lua5.5,interpreter' per_row='5':
    python3 tools/bench_bars.py --builds "{{builds}}" --clamp "{{clamp}}" --per-row {{per_row}}
# Hardware counters (`perf stat`) for this checkout's build of `profile`
# (`release` or `unsafe`) and revision `ref`'s (built as `_build-vs` builds
# them) on one benchmark, each pinned as `hyperfine` runs it and repeated `runs`
# times.
perf-stat-vs ref benchmark times='10' runs='5' profile='unsafe': (_build-vs ref)
    just _luac {{benchmark}}
    taskset -c {{CPU}} perf stat -r {{runs}} -e task-clock,cycles,instructions,branches,branch-misses,L1-icache-load-misses,iTLB-load-misses \
        target/compare/{{ref}}/target/{{profile}}/bench working/{{benchmark}}.bin {{times}} > /dev/null
    taskset -c {{CPU}} perf stat -r {{runs}} -e task-clock,cycles,instructions,branches,branch-misses,L1-icache-load-misses,iTLB-load-misses \
        ./target/{{profile}}/bench working/{{benchmark}}.bin {{times}} > /dev/null
# `perf-stat-vs` over HYPERFINES (tools/perf_stat_vs.py): instructions, branches
# and cycles of revision `ref`'s build of `profile` and this checkout's on each
# run, `runs` times each: the work done, apart from layout.
perf-stats-vs ref runs='3' profile='unsafe': (_build-vs ref)
    python3 tools/perf_stat_vs.py --cpu {{CPU}} --runs {{runs}} target/compare/{{ref}}/target/{{profile}}/bench ./target/{{profile}}/bench {{HYPERFINES}}

# Compare this checkout's release build with and without cargo feature
# `feature` on one benchmark: the feature's build is in target/features/<feature>.
hyperfine-feature feature benchmark times='10':
    just _luac {{benchmark}}
    cargo build --release --bin bench
    cargo build --release --features {{feature}} --bin bench --target-dir target/features/{{feature}}
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}-{{feature}}.md \
        -n default "./target/release/bench working/{{benchmark}}.bin {{times}}" \
        -n {{feature}} "target/features/{{feature}}/release/bench working/{{benchmark}}.bin {{times}}"
hyperfine-jit benchmark:
    just _luac {{benchmark}}
    cargo build --release --bin bench
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown working/hyperfine-{{benchmark}}-jit.md \
        "./target/release/bench working/{{benchmark}}.bin"
hyperfine-unsafe benchmark: unsafe-compile
    just _luac {{benchmark}}
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown working/hyperfine-{{benchmark}}-unsafe.md \
        "./target/unsafe/bench working/{{benchmark}}.bin"


# The benchmarks lunacy runs, as `benchmark:times`, each run enough times for a
# stable mean; life twice, as for `hyperfines-traces`. euler14's count is the
# bound of its search.
HYPERFINES := "life:1000 life:5000 nbody:10 queens:3000 fannkuch_redux:150 euler14:1000000 nsieve_bit:10 nsieve:9 binarytrees:2 partialsums:2000000 series:2 mandelbrot:1000 mandelbrot_bit:1000 array3d:120 quicksort:300000 table_cmpsort:100000 recursive_fib:35"

# Which benchmarks lunacy runs (tools/bench_runs.py): each of lua_benchmarking's,
# or those named, at `fraction` of its benchinfo.json scaling, against LuaJIT.
bench-runs fraction='0.1' *benchmarks:
    python3 tools/bench_runs.py --fraction {{fraction}} {{benchmarks}}

# The array part stores and hash field stores each run of HYPERFINES does, by
# what the specializer knew of each stored value's type: nothing, that it's a
# number, or its type (feature `store_types`), from the run's counters.
store-types:
    #!/usr/bin/env bash
    set -euo pipefail
    cargo build --release --features store_types --bin bench --target-dir target/store_types
    for run in {{HYPERFINES}}; do
        benchmark=${run%:*}; times=${run#*:}
        just _luac $benchmark > /dev/null
        echo "$benchmark $times: $(cd working && ../target/store_types/release/bench $benchmark.bin $times | grep -o 'array_stores([^)]*) field_stores([^)]*)' | tail -1)"
    done

# lunacy's interpreter alone (no JIT) on a benchmark, into the history as
# `hyperfine-full` records it: for a change to the interpreter, without timing
# every other implementation again.
hyperfine-interpreter benchmark times='10': interpreter-compile
    just _luac {{benchmark}}
    taskset -c {{CPU}} hyperfine -i --warmup {{WARMUP}} --export-json working/hyperfine-{{benchmark}}-{{times}}-interpreter.json \
        -n interpreter "./target/interpreter/release/bench working/{{benchmark}}.bin {{times}}"
    python3 tools/bench_history.py record working/hyperfine-{{benchmark}}-{{times}}-interpreter.json --benchmark {{benchmark}} --arg {{times}}

# `hyperfine-interpreter` over HYPERFINES.
hyperfines-interpreter:
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{HYPERFINES}}; do just hyperfine-interpreter ${run%:*} ${run#*:}; done

# `hyperfine` over HYPERFINES.
hyperfines:
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{HYPERFINES}}; do just hyperfine ${run%:*} ${run#*:}; done
    python3 tools/bench_history.py report

# The JIT code size of each benchmark of HYPERFINES run by checkout `dir`
# (this one, or revision `ref`'s compare worktree) on the benchmark as that
# checkout compiles it, from its annotated
# disassembly (as `jit-disasm` makes it), into the size history
# (tools/bench_history.py record-size). A benchmark whose run fails is left
# out, its output in working/jit-size-<benchmark>.log.
_jit-sizes dir ref='':
    #!/usr/bin/env bash
    set -euo pipefail
    mkdir -p {{dir}}/working
    for run in {{HYPERFINES}}; do
        benchmark=${run%:*}; times=${run#*:}
        # The benchmark as the checkout itself compiles it: an older one can't
        # run a newer one's bytecode. Before its recipes made their artifacts
        # in working/, `_luac` wrote <benchmark>.bin at the top.
        rm -f {{dir}}/working/$benchmark.bin {{dir}}/$benchmark.bin
        (cd {{dir}} && just _luac $benchmark > /dev/null)
        [ -f {{dir}}/working/$benchmark.bin ] || mv {{dir}}/$benchmark.bin {{dir}}/working/
        rm -f {{dir}}/working/jit_disasm.txt
        if (cd {{dir}}/working && cargo run --profile unsafe --no-default-features --features "unsafe jit_disasm" --bin bench \
                --target-dir ../target/jit_disasm -Z build-std="core,std,panic_abort" -- $benchmark.bin $times) \
                > working/jit-size-$benchmark.log 2>&1; then
            python3 tools/bench_history.py record-size {{dir}}/working/jit_disasm.txt --benchmark $benchmark --arg $times {{ if ref == "" { "" } else { "--ref " + ref } }} \
                || echo "skipped $benchmark $times: no size recorded"
        else
            echo "skipped $benchmark $times: its run failed (working/jit-size-$benchmark.log)"
        fi
    done

# The JIT code size of each benchmark of HYPERFINES, into the size history
# (see `_jit-sizes`).
jit-sizes: (_jit-sizes ".")

# Revision `ref`'s JIT code size on each benchmark of HYPERFINES, into the size
# history (see `_jit-sizes`), from its compare worktree: to fill in commits
# before sizes were kept. A revision without the `jit_disasm` feature has none.
jit-size-rev ref:
    #!/usr/bin/env bash
    set -euo pipefail
    just _compare-worktree {{ref}}
    if ! grep -q '^jit_disasm' target/compare/{{ref}}/Cargo.toml; then
        echo "{{ref}}: no jit_disasm feature, so no JIT code sizes"
        exit 1
    fi
    just _jit-sizes target/compare/{{ref}} {{ref}}

# This checkout's JIT code size on each benchmark of HYPERFINES against revision
# `ref`'s, both into the size history.
jit-size-vs ref: (jit-size-rev ref) jit-sizes
    python3 tools/bench_history.py sizes-vs {{ref}}

# The benchmark history of this checkout: times (`hyperfines`), JIT code sizes
# (`jit-sizes`), the charts of both (`bench-history`), and the latest times as
# bars (`bench-bars`).
bench: hyperfines jit-sizes bench-history bench-bars

# `hyperfine-full` over HYPERFINES.
hyperfines-full:
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{HYPERFINES}}; do just hyperfine-full ${run%:*} ${run#*:}; done
    python3 tools/bench_history.py report

# Compare this checkout's release build under each feature set in `sets`
# (comma separated features, or `none`) on one benchmark: each built in turn
# into target/release and copied to target/features/<set>/bench.
hyperfine-features benchmark times +sets:
    #!/usr/bin/env bash
    set -euo pipefail
    just _luac {{benchmark}}
    commands=()
    for set in {{sets}}; do
        features=$set; if [ $set = none ]; then features=""; fi
        cargo build --release --bin bench --features "$features"
        mkdir -p target/features/$set && cp target/release/bench target/features/$set/bench
        commands+=(-n $set "target/features/$set/bench working/{{benchmark}}.bin {{times}}")
    done
    taskset -c {{CPU}} hyperfine --warmup {{WARMUP}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}-features.md "${commands[@]}"

# `hyperfine-features` over HYPERFINES, then every comparison's table.
hyperfines-features +sets:
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{HYPERFINES}}; do just hyperfine-features ${run%:*} ${run#*:} {{sets}}; done
    for run in {{HYPERFINES}}; do echo "${run%:*} ${run#*:}"; tail -n +3 working/hyperfine-${run%:*}-${run#*:}-features.md; done

# `hyperfine-vs ref` over HYPERFINES, then every comparison's table.
hyperfines-vs ref:
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{HYPERFINES}}; do just hyperfine-vs {{ref}} ${run%:*} ${run#*:}; done
    for run in {{HYPERFINES}}; do tail -n 4 working/hyperfine-${run%:*}-${run#*:}-vs-{{ref}}.md; done
    python3 tools/bench_history.py report

all: test benchmarks (hyperfine "binarytrees")
