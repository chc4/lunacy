set shell := ["bash", "-c"]
TEST_FEATURES := "counters graph jit gas gc_sanitize"
# Runs hyperfine makes of each command before timing it, so the CPU has ramped
# up and caches are warm.
WARMUP := "3"
# The most runs hyperfine makes of a command: with no limit, it may never stop timing one that
# runs for a few milliseconds.
MAX_RUNS := "300"
# The core hyperfine and the commands it times are pinned to (`taskset`), so a
# run never migrates onto a core that has not ramped up.
CPU := "2"
# A lock every run that times or samples code holds while it runs (`flock`), so
# that nothing else from any checkout or agent on the machine runs with it and
# skews it: a timed or sampled run holds it alone, and each build, test or run
# through cargo shares it (`SHARED`), so a measurement waits for those and they
# wait for it. Each command takes it, never a recipe calling another, which
# would wait on itself; `cargo watch`, which never ends, doesn't.
BENCH_LOCK := env_var_or_default("LUNACY_BENCH_LOCK", "/tmp/lunacy-bench.lock")
# The prefix of a timed command: the lock, then pinned to `CPU`.
TIMED := "flock " + BENCH_LOCK + " taskset -c " + CPU
# The prefix of a sampled command: the lock.
SAMPLED := "flock " + BENCH_LOCK
# The prefix of a build, test or other run that loads the machine without
# measuring: the lock shared, so that any number run together, but none while a
# timed or sampled run holds it, nor one while they do.
SHARED := "flock -s " + BENCH_LOCK

# Every test: `test`, then `test-stencils`.
tests: test test-stencils

# The library's unit tests whose names contain `filter`, as `test` runs them:
# quicker than the whole suite while iterating.
unit filter:
    {{SHARED}} cargo test --features "gc_sanitize" --lib {{filter}}

# Run lunacy against the golden testcases
[env("RUST_BACKTRACE","1")]
test:
    # GC correctness tests
    {{SHARED}} cargo test "gc::" --features "gc_test,gc_sanitize" -- --test-threads 1
    # Normal interpreter tests
    {{SHARED}} cargo test --features "gc_sanitize"
    # Interpreter GC stress test
    {{SHARED}} cargo test --features "gc_stress gc_sanitize"
    # Heap reset frees (no leak); needs the real finalizer, so runs without gc_sanitize
    {{SHARED}} cargo test --test gc_reset_frees
    # The golden tests with random gas, a new seed each time, which a failure prints to
    # rerun it with (`just golden-gas <seed>`)
    just golden-gas

# Copy&patch window stencils (src/window.rs) as the JIT will use them: built
# in release, so the stencils checked are the ones the JIT copies (a build
# with any other optimization, codegen units or LTO compiles them to different
# code: `tools/stencil_diff.py` compares two builds'). The window unit
# tests also run in `just test` (debug); this runs them against optimized
# stencils, then the golden suite with `check_windows`: every window op the
# interpreter executes is also copy&patched and run natively, and the results
# must match. (At opt-level 0,
# `NumericRR` keeps a jump table from the unfolded `match OP`, which the
# copier rejects: the check skips it and the JIT calls into the interpreter.)
STENCIL_OPT := "--release"
[env("RUST_BACKTRACE","1")]
test-stencils:
    {{SHARED}} cargo test --features check_windows --lib window:: {{STENCIL_OPT}}
    {{SHARED}} cargo test --features check_windows --test golden_tests {{STENCIL_OPT}}

# A benchmark's run traced (feature `tracing`) to working/lunacy.fxt, a
# Perfetto trace (https://ui.perfetto.dev opens it), and summarized with
# Perfetto's trace processor: its JIT compiles, and its bailouts by reason and
# by where they are. Built as the benchmarks are timed: the unsafe profile.
trace benchmark times='10' features='unsafe':
    just _luac {{benchmark}}
    {{SHARED}} cargo build --profile unsafe --no-default-features --features "{{features}} tracing" --bin bench \
        --target-dir target/tracing -Z build-std="core,std,panic_abort"
    cd working && {{SHARED}} ../target/tracing/unsafe/bench {{benchmark}}.bin {{times}} > /dev/null
    python3 tools/perfetto_summary.py working/lunacy.fxt

# `trace` of revision `ref` (as for `hyperfine-vs`), from its compare worktree,
# its trace in working/lunacy-<ref>.fxt.
trace-rev ref benchmark times='10' features='unsafe':
    #!/usr/bin/env bash
    set -euo pipefail
    just _compare-worktree {{ref}}
    dir=target/compare/{{ref}}
    (cd $dir && just _luac {{benchmark}} > /dev/null)
    (cd $dir && {{SHARED}} cargo build --profile unsafe --no-default-features --features "{{features}} tracing" --bin bench \
        --target-dir target/tracing -Z build-std="core,std,panic_abort")
    (cd $dir/working && {{SHARED}} ../target/tracing/unsafe/bench {{benchmark}}.bin {{times}} > /dev/null)
    mv $dir/working/lunacy.fxt working/lunacy-{{ref}}.fxt

# Each benchmark of HYPERFINES traced at revision `ref` and in this checkout,
# their hash keys and versions compared (tools/hash_key_stats.py).
hash-keys-vs ref features='unsafe':
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{HYPERFINES}}; do
        benchmark=${run%:*}; times=${run#*:}
        just trace-rev {{ref}} $benchmark $times "{{features}}" > /dev/null 2>&1 || { echo "skipped $benchmark: its traced run at {{ref}} failed"; continue; }
        mv working/lunacy-{{ref}}.fxt working/hash-keys-$benchmark-{{ref}}.fxt
        just trace $benchmark $times "{{features}}" > /dev/null 2>&1 || { echo "skipped $benchmark: its traced run failed"; continue; }
        mv working/lunacy.fxt working/hash-keys-$benchmark.fxt
        python3 tools/hash_key_stats.py $benchmark working/hash-keys-$benchmark-{{ref}}.fxt working/hash-keys-$benchmark.fxt
    done

# A golden test's run traced (feature `tracing`), as `trace` traces a
# benchmark's: lua_tests/<name>.lua in the golden harness, built in release with
# `features`, to working/lunacy.fxt, then summarized. A failing run still
# leaves its trace.
trace-golden name features='check_windows':
    -LUNACY_GOLDEN={{name}} {{SHARED}} cargo test --release --features "{{features}} tracing" --test golden_tests test_golden
    mv lunacy.fxt working/lunacy.fxt
    python3 tools/perfetto_summary.py working/lunacy.fxt

# `trace-golden` of this checkout's lua_tests/<name>.lua at revision `ref`, from
# its compare worktree (as for `hyperfine-vs`): its trace in
# working/lunacy-golden-<name>-<ref>.fxt, its test output in
# working/golden-<name>-<ref>.log. For when a test's versions grew, and which
# revision made them.
trace-golden-rev ref name features='check_windows':
    #!/usr/bin/env bash
    set -uo pipefail
    just _compare-worktree {{ref}}
    dir=target/compare/{{ref}}
    cp lua_tests/{{name}}.lua $dir/lua_tests/{{name}}.lua
    (cd $dir && LUNACY_GOLDEN={{name}} {{SHARED}} cargo test --release --features "{{features}} tracing" --test golden_tests test_golden) > working/golden-{{name}}-{{ref}}.log 2>&1
    grep -aE "test result|panicked at|Output mismatch" working/golden-{{name}}-{{ref}}.log | head -2
    mv $dir/lunacy.fxt working/lunacy-golden-{{name}}-{{ref}}.fxt

# `trace`'s summary of working/lunacy.fxt again.
show-trace:
    python3 tools/perfetto_summary.py working/lunacy.fxt

# SQL against `trace`'s working/lunacy.fxt (tools/trace_sql.py): the
# specializer's version choices, compiled versions and blocks are the views
# spec_version, spec_block and block_summary.
trace-sql query:
    python3 tools/trace_sql.py "{{query}}"

# Each of `runs` (`benchmark:times`) traced, and its versions (`point_versions`):
# by function, its points with the most, and the inlined copies of points with the
# most (`site_versions`), in working/versions-<benchmark>.txt.
version-summaries +runs:
    #!/usr/bin/env bash
    set -uo pipefail
    for run in {{runs}}; do
        benchmark=${run%:*}; times=${run#*:}
        out=working/versions-$benchmark.txt
        if ! just trace $benchmark $times > $out 2>&1; then echo "$benchmark: its traced run failed"; continue; fi
        { python3 tools/trace_sql.py "SELECT outcome, COUNT(*) AS jumps FROM spec_version GROUP BY outcome ORDER BY jumps DESC"
          python3 tools/trace_sql.py "SELECT COUNT(*) AS points, SUM(created) AS created, SUM(live) AS live, SUM(unreachable) AS unreachable FROM point_versions"
          python3 tools/trace_sql.py "SELECT line, COUNT(*) AS points, SUM(created) AS created, SUM(live) AS live, SUM(unreachable) AS unreachable, MAX(live + unreachable) AS most FROM point_versions GROUP BY line ORDER BY live DESC LIMIT 10"
          python3 tools/trace_sql.py "SELECT line, pc, created, live, unreachable, evicted, forgotten FROM point_versions ORDER BY live + unreachable DESC LIMIT 10"
          python3 tools/trace_sql.py "SELECT inline, pc, created, live, unreachable, evicted, forgotten FROM site_versions ORDER BY live + unreachable DESC LIMIT 15"; } > $out 2>&1
    done

# Each golden test's versions, as `trace-golden` traces it: live at the end, the most live at one
# point, and made in all (tools/trace_sql.py's point_versions).
golden-versions +names:
    #!/usr/bin/env bash
    set -uo pipefail
    for name in {{names}}; do
        just trace-golden "$name" > /dev/null 2>&1
        echo "$name: $(python3 tools/trace_sql.py 'SELECT sum(live) AS live, max(live) AS most, sum(created) AS created FROM point_versions' | tail -1)"
    done

# `golden-versions` at revision `ref`, each test traced as `trace-golden-rev`
# traces it.
golden-versions-rev ref +names:
    #!/usr/bin/env bash
    set -uo pipefail
    for name in {{names}}; do
        just trace-golden-rev {{ref}} "$name" > /dev/null 2>&1
        echo "$name: $(python3 tools/trace_sql.py --trace working/lunacy-golden-$name-{{ref}}.fxt 'SELECT sum(live) AS live, max(live) AS most, sum(created) AS created FROM point_versions' | tail -1)"
    done

# The named golden tests (lua_tests/<name>.lua), each against its expected
# output, in one debug build with `test`'s golden suite's features: quicker than
# the whole suite while iterating.
golden +names:
    LUNACY_GOLDEN={{replace(names, " ", ",")}} {{SHARED}} cargo test --features gc_sanitize --test golden_tests test_golden

# The golden tests, each with random gas (`LUNACY_GOLDEN_GAS_SEED`, from `seed`, else
# a random one, printed): JIT code stopped anywhere must leave a test's output as it
# was, so a run failing is a JIT miscompile or an exit that loses state. Rerun with its
# seed, and bisect the test with `gas-bisect`. Its whole output in working/golden-gas.log.
golden-gas seed='':
    #!/usr/bin/env bash
    set -euo pipefail
    seed="{{seed}}"
    [ -n "$seed" ] || seed=$RANDOM$RANDOM
    echo "seed $seed"
    status=0
    LUNACY_GOLDEN_GAS_SEED=$seed {{SHARED}} cargo test --features "gc_sanitize gas" --test golden_tests test_golden -- --nocapture > working/golden-gas.log 2>&1 || status=$?
    grep -E "panicked|ran past|test result|mismatch" -B1 working/golden-gas.log | grep -v "^--" | tail -n 20
    exit $status

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
    cd working && {{SHARED}} cargo run --release --no-default-features --features graph --bin bench -- {{benchmark}}.bin {{times}}
    python3 tools/window_runs.py working/func_*.dot

# The JIT's window allocation for a benchmark, in working/window_dump.txt: each compiled
# block's entry window, then per residual its loads, stores and moves, what each
# jump transfers, and the window after it.
# With `ref`, revision `ref`'s (in target/compare/<ref>, as for `hyperfine-vs`)
# on this checkout's benchmark, in target/compare/<ref>/window_dump.txt.
# `build` is the release build or the unsafe one, which compile different
# regions: their stencils and what runs before a block gets hot differ.
# The allocator code a benchmark's run executed most, from its window dump
# (tools/window_hot.py): `args` as the tool takes them (`--blocks`, `--top N`).
window-hot benchmark times='20' *args: (window-dump benchmark times)
    python3 tools/window_hot.py working/window_dump.txt {{args}}

window-dump benchmark times='20' ref='' build='release':
    #!/usr/bin/env bash
    set -euo pipefail
    just _luac {{benchmark}}
    if [ "{{build}}" = unsafe ]; then
        flags=(--profile unsafe --no-default-features --features "unsafe window_dump" --target-dir target/window_dump -Z build-std=core,std,panic_abort)
    else
        flags=(--release --features window_dump)
    fi
    if [ -z "{{ref}}" ]; then
        cd working && {{SHARED}} cargo run "${flags[@]}" --bin bench -- {{benchmark}}.bin {{times}}
    else
        just _compare-worktree {{ref}}
        bin=$(realpath working/{{benchmark}}.bin)
        (cd target/compare/{{ref}} && {{SHARED}} cargo run "${flags[@]}" --bin bench -- $bin {{times}})
    fi

# The size of each window op's stencil a benchmark's JIT code copies, in the
# release build and the unsafe one, as the copier reports them (feature
# `jit_disasm`): the body it splats (bytes and instructions) and the stencil
# function it copied it from, in working/stencil_sizes-release.txt and
# working/stencil_sizes-unsafe.txt.
stencil-sizes benchmark='queens' times='10':
    just _luac {{benchmark}}
    cd working && {{SHARED}} cargo run --release --features jit_disasm --bin bench --target-dir ../target/jit_disasm \
        -- {{benchmark}}.bin {{times}} > /dev/null
    mv working/stencil_sizes.txt working/stencil_sizes-release.txt
    cd working && {{SHARED}} cargo run --profile unsafe --no-default-features --features "unsafe jit_disasm" --bin bench \
        --target-dir ../target/jit_disasm -Z build-std="core,std,panic_abort" -- {{benchmark}}.bin {{times}} > /dev/null
    mv working/stencil_sizes.txt working/stencil_sizes-unsafe.txt
    head -25 working/stencil_sizes-unsafe.txt

# Cold code in every window op's stencil (see tools/stencil_cold.py), in the
# release and unsafe builds, and every stencil's assembly in
# working/stencils-release.s and working/stencils-unsafe.s.
stencil-cold: unsafe-compile
    {{SHARED}} cargo build --release --bin bench
    {{SHARED}} cargo build --release --features jit_disasm --bin demangle --target-dir target/jit_disasm
    mkdir -p working
    python3 tools/stencil_cold.py target/release/bench --dump working/stencils-release.s
    python3 tools/stencil_cold.py target/unsafe/bench --dump working/stencils-unsafe.s

# A benchmark's JIT code, disassembled when the VM drops it and annotated with
# what emitted it (regions, blocks, residuals, thunk stubs, the blocks and
# helpers branches go to), in working/jit_disasm.txt. Built as `unsafe-compile`
# builds, with `features` (by default the unsafe build's).
jit-disasm benchmark times='10' features='unsafe':
    just _luac {{benchmark}}
    cd working && {{SHARED}} cargo run --profile unsafe --no-default-features --features "{{features}} jit_disasm" --bin bench \
        --target-dir ../target/jit_disasm -Z build-std="core,std,panic_abort" -- {{benchmark}}.bin {{times}} > /dev/null
    @echo working/jit_disasm.txt

# Where a benchmark's JIT code goes, in bytes (tools/jit_code_size.py): by
# function, by kind of residual, and the largest blocks, from its annotated
# disassembly (`jit-disasm`).
jit-code-size benchmark times='10': (jit-disasm benchmark times)
    python3 tools/jit_code_size.py working/jit_disasm.txt

# How often a benchmark's compiled code runs (tools/block_counts.py): its compiled blocks' bytes by
# how many times each block's code ran, counted exactly (feature `block_counts`), and the functions
# with the most code that ran rarely. working/block_counts.txt has each block's counts.
block-counts benchmark times='10': (jit-disasm benchmark times "unsafe block_counts")
    python3 tools/block_counts.py working/jit_disasm.txt working/block_counts.txt

# `jit-code-size` of each of `runs` (`benchmark:times`, as HYPERFINES has them):
# each one's in working/jit-code-size-<benchmark>.txt.
jit-code-sizes +runs:
    #!/usr/bin/env bash
    set -uo pipefail
    for run in {{runs}}; do
        benchmark=${run%:*}; times=${run#*:}
        just jit-code-size $benchmark $times > working/jit-code-size-$benchmark.txt 2>&1 || echo "$benchmark: its run failed"
    done

# `jit-disasm` of revision `ref`, from its compare worktree (as for
# `hyperfine-vs`), on this checkout's compiled benchmark: in
# working/jit_disasm-<ref>.txt.
jit-disasm-rev ref benchmark times='10' features='unsafe':
    #!/usr/bin/env bash
    set -euo pipefail
    just _luac {{benchmark}}
    just _compare-worktree {{ref}}
    bin=$(realpath working/{{benchmark}}.bin)
    dir=target/compare/{{ref}}
    mkdir -p $dir/working
    (cd $dir/working && {{SHARED}} cargo run --profile unsafe --no-default-features --features "{{features}} jit_disasm" --bin bench \
        --target-dir ../target/jit_disasm -Z build-std="core,std,panic_abort" -- $bin {{times}} > /dev/null)
    mv $dir/working/jit_disasm.txt working/jit_disasm-{{ref}}.txt

# How a benchmark's JIT code differs from revision `ref`'s, in bytes
# (tools/jit_code_size.py --vs): by function, by kind of residual, and by pc.
jit-code-size-vs ref benchmark times='10': (jit-disasm-rev ref benchmark times) (jit-disasm benchmark times)
    python3 tools/jit_code_size.py working/jit_disasm.txt --vs working/jit_disasm-{{ref}}.txt --top 30

# A golden test's JIT code, in bytes, as `jit-code-size` measures a benchmark's:
# lua_tests/<name>.lua run by the unsafe build, as `jit-disasm` builds it (with
# `magic`, for the tests that force JIT compiling).
jit-code-size-test name:
    just _luac-test {{name}}
    rm -f working/jit_disasm.txt
    cd working && {{SHARED}} cargo run --profile unsafe --no-default-features --features "unsafe magic jit_disasm" --bin lunacy \
        --target-dir ../target/jit_disasm -Z build-std="core,std,panic_abort" -- {{name}}.bin > /dev/null
    python3 tools/jit_code_size.py working/jit_disasm.txt

# How much machine code LuaJIT's JIT generates for a benchmark, and whether it
# flushes its traces partway (tools/luajit_mcode.lua), to compare with
# `jit-code-size`.
luajit-mcode benchmark times='10':
    just _luajitc {{benchmark}}
    luajit tools/luajit_mcode.lua working/{{benchmark}}.luajit.bin {{times}}

# Profile a benchmark with IBS (AMD's precise sampling: a sample is the
# instruction that ran, with no skid), every `period` cycles, built as
# `jit-disasm` builds with the perf map too, and join the samples on the JIT's
# code to its disassembly (tools/jit_samples.py): by what emitted the code, by kind
# of code and stack slot traffic, and,
# with `op` (a disassembly note, like `PushFrame`), that code's instructions
# summed over its copies. working/jit-profile.data, and the sampled
# disassembly with counts in working/jit_samples.txt. `event` samples another event
# every `period` of it in place of IBS, as a raw counter (`r47`, misaligned
# accesses on Zen 2): a counter's sample is taken at its overflow interrupt, so it
# lands some instructions after the one that counted. `only` keeps the IBS samples of
# ops with that flag of IBS's op data set (`DcMisAcc`, a misaligned access), from
# its raw data (tools/ibs_samples.py).
jit-profile benchmark times='10' op='' period='20000' features='unsafe' event='ibs_op//' only='':
    just _luac {{benchmark}}
    {{SHARED}} cargo build --profile unsafe --no-default-features --features "{{features}} perf jit_disasm" --bin bench \
        --target-dir target/jit_disasm -Z build-std="core,std,panic_abort"
    cd working && {{SAMPLED}} perf record -e {{event}} -c {{period}} {{ if only != "" { "-R" } else { "" } }} -o jit-profile.data ../target/jit_disasm/unsafe/bench {{benchmark}}.bin {{times}} > /dev/null
    {{ if only != "" { "cd working && perf report -D -i jit-profile.data | python3 ../tools/ibs_samples.py " + only + " jit-profile.data > jit-profile.samples" } else { "cd working && perf script -i jit-profile.data -F ip,sym > jit-profile.samples" } }}
    python3 tools/jit_samples.py working/jit_disasm.txt working/jit-profile.samples --out working/jit_samples.txt --classes {{ if op != "" { "--op '" + op + "'" } else { "" } }}

# `jit-profile` of revision `ref`, from its compare worktree (as for `hyperfine-vs`), on this
# checkout's compiled benchmark: its sampled disassembly in working/jit_samples-<ref>.txt.
jit-profile-rev ref benchmark times='10' period='20000' features='unsafe' event='ibs_op//':
    #!/usr/bin/env bash
    set -euo pipefail
    just _luac {{benchmark}}
    just _compare-worktree {{ref}}
    bin=$(realpath working/{{benchmark}}.bin)
    dir=target/compare/{{ref}}
    mkdir -p $dir/working
    (cd $dir && {{SHARED}} cargo build --profile unsafe --no-default-features --features "{{features}} perf jit_disasm" --bin bench \
        --target-dir target/jit_disasm -Z build-std="core,std,panic_abort")
    (cd $dir/working && {{SAMPLED}} perf record -e {{event}} -c {{period}} -o jit-profile.data ../target/jit_disasm/unsafe/bench $bin {{times}} > /dev/null)
    (cd $dir/working && perf script -i jit-profile.data -F ip,sym > jit-profile.samples)
    python3 tools/jit_samples.py $dir/working/jit_disasm.txt $dir/working/jit-profile.samples --out working/jit_samples-{{ref}}.txt --classes

# `jit-profile` of each of `runs` (`benchmark:times`, as HYPERFINES has them): each one's
# summary in working/jit-profile-<benchmark>.txt and its sampled disassembly in
# working/jit_samples-<benchmark>.txt.
jit-profiles +runs:
    #!/usr/bin/env bash
    set -uo pipefail
    for run in {{runs}}; do
        benchmark=${run%:*}; times=${run#*:}
        just jit-profile $benchmark $times > working/jit-profile-$benchmark.txt 2>&1 || echo "$benchmark: its profiled run failed"
        cp working/jit_samples.txt working/jit_samples-$benchmark.txt
    done

# Save a benchmark's window dump as bench/window_dumps/<benchmark>.<name>.txt, a
# reference to compare window allocators against with `just window-dump-stats`.
window-dump-save benchmark name times='20':
    just window-dump {{benchmark}} {{times}}
    mkdir -p bench/window_dumps
    cp working/window_dump.txt bench/window_dumps/{{benchmark}}.{{name}}.txt

# A lua_tests program's window allocation under streaming allocation and each
# trace-building policy, as bench/window_dumps/<name>.<policy>.txt.
window-dump-policies name: (_luac-test name)
    {{SHARED}} cargo build --release --features window_dump --bin lunacy
    mkdir -p bench/window_dumps
    for policy in streaming single unidirectional bidirectional; do (cd working && LUNACY_TRACES=$policy ../target/release/lunacy {{name}}.bin > /dev/null) && cp working/window_dump.txt bench/window_dumps/{{name}}.$policy.txt; done

# Executed loads, stores and moves of each benchmark, run `times` times, under
# streaming allocation and unidirectional traces, from their window dumps; a
# benchmark that fails (lunacy lacks some of Lua) says why.
window-dump-compare times +benchmarks:
    {{SHARED}} cargo build --release --features window_dump --bin bench
    for b in {{benchmarks}}; do just _luac $b || continue; for policy in streaming unidirectional; do if (cd working && LUNACY_TRACES=$policy timeout 600 ../target/release/bench $b.bin {{times}} > /dev/null 2> ../target/window-dump-compare.err); then python3 tools/window_dump_stats.py --raw working/window_dump.txt | tail -1 | sed "s|^working/window_dump.txt|$b $policy|"; else echo "$b $policy: failed: $(grep -A1 -m1 panicked target/window-dump-compare.err | tail -1)"; fi; done; done

# The loads, stores and moves in window dumps, over all blocks and hot ones.
window-dump-stats *dumps='bench/window_dumps/*.txt':
    python3 tools/window_dump_stats.py {{dumps}}

[env("RUST_LOG", "debug")]
[env("RUST_BACKTRACE","1")]
test-debug:
    {{SHARED}} cargo test --features "gc_sanitize" -- --nocapture

watch:
    cargo watch -- cargo test

[env("RUST_LOG", "debug")]
debug name: (_luac-test name)
    cd working && time {{SHARED}} cargo run --no-default-features --features "{{TEST_FEATURES}}" --bin lunacy -- {{name}}.bin

debug-jit name: (_luac-test name)
    cd working && time {{SHARED}} cargo run --no-default-features --features "{{TEST_FEATURES}} immediate_jit" --bin lunacy -- {{name}}.bin

release name: (_luac-test name)
    cd working && time {{SHARED}} cargo run --release --no-default-features --features "{{TEST_FEATURES}}" --bin lunacy -- {{name}}.bin

# lua_tests/<name>.lua under gdb, with `gdb_args` (say "-batch -ex run -ex bt" for the
# backtrace where it crashes), built with `features` too (`alloc_debug` to find a write past or
# after an allocation).
gdb-test name gdb_args='' features='': (_luac-test name)
    {{SHARED}} cargo build --release --bin lunacy --features "{{features}}"
    gdb {{gdb_args}} --args ./target/release/lunacy working/{{name}}.bin

# Compile lua_tests/<name>.lua to working/<name>.bin.
# `source`'s residual graphs (working/func_<line>.dot), run by the release
# `lunacy` with TEST_FEATURES and `gas` of it: a gas-bisect's run just short of
# going wrong.
graph-gas source gas:
    {{SHARED}} cargo build --release --features "gas graph" --bin lunacy
    luac5.1 -o working/gas-bisect.bin {{source}}
    cd working && LUNACY_GAS={{gas}} {{SAMPLED}} ../target/release/lunacy gas-bisect.bin > graph-gas.log 2>&1

# `source`'s JIT code, disassembled and annotated as `jit-disasm` makes it, run by
# the release `lunacy` with `gas` of it, as `gas-bisect` runs it: the code a run
# just short of going wrong ran, in working/jit_disasm.txt.
gas-disasm source gas:
    {{SHARED}} cargo build --release --features "gas jit_disasm" --bin lunacy --target-dir target/gas_disasm
    luac5.1 -o working/gas-bisect.bin {{source}}
    -cd working && LUNACY_GAS={{gas}} {{SAMPLED}} ../target/gas_disasm/release/lunacy gas-bisect.bin > gas-disasm.log 2>&1

# The last `lines` of `source`'s debug log (RUST_LOG=debug), run by the release
# `lunacy` with `gas` of it, as `gas-bisect` runs it: the residuals the interpreter
# ran after the JIT code's gas ran out, to where the run goes wrong. In
# working/gas-log.txt.
gas-log source gas lines='400':
    {{SHARED}} cargo build --release --features gas --bin lunacy
    luac5.1 -o working/gas-bisect.bin {{source}}
    -cd working && RUST_LOG=debug LUNACY_GAS={{gas}} {{SAMPLED}} ../target/release/lunacy gas-bisect.bin 2>&1 | tail -n {{lines}} > gas-log.txt

# The least gas with which `source`'s run goes wrong, against `reference`'s
# (Lua 5.1, or luajit for a program needing `bit`; tools/gas_bisect.py): where
# JIT code miscompiles, run by the release `lunacy` with `gas`, and none of the
# test features' checks, which slow a long run past the bisection's limit.
gas-bisect source signature='' reference='lua5.1':
    {{SHARED}} cargo build --release --features gas --bin lunacy
    luac5.1 -o working/gas-bisect.bin {{source}}
    {{SAMPLED}} python3 tools/gas_bisect.py working/gas-bisect.bin {{source}} target/release/lunacy --signature "{{signature}}" --reference {{reference}}

# Where JIT code stops for each gas in `range` (`from:to[:step]`), as `gas-bisect`
# runs `source`: the residual, and the frame base the code held against the
# interpreter's (tools/gas_bisect.py --scan).
gas-scan source range:
    {{SHARED}} cargo build --release --features gas --bin lunacy
    luac5.1 -o working/gas-bisect.bin {{source}}
    {{SAMPLED}} python3 tools/gas_bisect.py working/gas-bisect.bin {{source}} target/release/lunacy --scan {{range}}

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
# tcvm's copy of a benchmark, as `_luac`, in working/<benchmark>.tcvm.lua: the Lua
# 5.5 bundle, calling `run_iter` with the count tcvm's command line gives (`arg`).
_tcvmc benchmark:
    #!/usr/bin/env bash
    set -euo pipefail
    mkdir -p working
    { python3 tools/bundle_bench.py {{benchmark}}; printf '\nrun_iter(tonumber(arg[1]))\n'; } > working/{{benchmark}}.tcvm.lua

_luauc benchmark:
    #!/usr/bin/env bash
    set -euo pipefail
    mkdir -p working
    { python3 tools/bundle_bench.py {{benchmark}}; printf '\nrun_iter(tonumber((...)))\n'; } > working/{{benchmark}}.luau

run benchmark *args:
    just _luac {{benchmark}}
    time {{SHARED}} cargo run --release --bin bench -- working/{{benchmark}}.bin {{args}}

[env("RUST_LOG", "debug")]
run-debug benchmark:
    just _luac {{benchmark}}
    time {{SHARED}} cargo run --bin bench -- working/{{benchmark}}.bin

# <name>.lua's residual graphs, as working/func_<line>.dot and .pdf.
graph name:
    mkdir -p working
    luac5.1 -o working/{{name}}.bin {{name}}.lua
    cd working && {{SHARED}} cargo run --features graph --bin lunacy -- {{name}}.bin
# lua_tests/<name>.lua's residual graphs as the golden test runner runs it
# (with its globals, such as `make_userdata`), in working/graphs/<name>.
graph-golden name:
    mkdir -p working/graphs/{{name}}
    LUNACY_GOLDEN={{name}} LUNACY_GRAPH_DIR=$PWD/working/graphs/{{name}} {{SHARED}} cargo test --features graph --test golden_tests test_golden
# `graph-golden`'s graphs of lua_tests/<name>.lua with `env` (an assignment, such as
# `LUNACY_NO_FUSION=1`) and without, side by side in working/graphs/<name>-vs/index.html
# (tools/graph_compare.py): searchable, over the residuals whose counts differ.
graph-golden-vs name env:
    #!/usr/bin/env bash
    set -euo pipefail
    rm -rf working/graphs/{{name}} working/graphs/{{name}}-with working/graphs/{{name}}-without
    env {{env}} just graph-golden {{name}}
    mv working/graphs/{{name}} working/graphs/{{name}}-with
    just graph-golden {{name}}
    mv working/graphs/{{name}} working/graphs/{{name}}-without
    python3 tools/graph_compare.py --before working/graphs/{{name}}-with --after working/graphs/{{name}}-without \
        --out working/graphs/{{name}}-vs --before-label "{{env}}" --after-label "default" \
        --title "{{name}}" --about "Residual graphs of lua_tests/{{name}}.lua from the golden runner, with {{env}} and without."
graph-release name:
    mkdir -p working
    luac5.1 -o working/{{name}}.bin {{name}}.lua
    cd working && {{SHARED}} cargo run --release --features graph --bin lunacy -- {{name}}.bin
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
        {{SHARED}} cargo build --release --features "$features" --bin bench --target-dir target/graph-$variant
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
    {{SHARED}} cargo build --release --features graph --bin bench --target-dir target/graph-current
    just _compare-worktree {{ref}}
    (cd target/compare/{{ref}} && {{SHARED}} cargo build --release --features graph --bin bench --target-dir target/graph)
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
    {{SHARED}} cargo build --release --bin lunacy
    gdb --args ./target/release/lunacy working/{{name}}.bin


baseline benchmark times='10':
    just _luac {{benchmark}}
    time lua5.1 bench.lua -- working/{{benchmark}}.bin {{times}}

gdb-benchmark benchmark:
    just _luac {{benchmark}}
    {{SHARED}} cargo build --release --bin bench
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
        (cd working && {{SAMPLED}} cargo flamegraph -c "record -F {{freq}} --call-graph fp -g" --profile flamegraph --no-default-features --features "{{features}}" --bin bench -- {{benchmark}}.bin {{times}})
        firefox -new-tab working/flamegraph.svg || true
    else
        dir=target/compare/{{ref}}
        just _compare-worktree {{ref}}
        bin=$(realpath working/{{benchmark}}.bin)
        svg=$(realpath working)/flamegraph-{{ref}}.svg
        (cd $dir && {{SAMPLED}} cargo flamegraph -c "record -F {{freq}} --call-graph fp -g" --profile flamegraph --no-default-features --features "{{features}}" --bin bench -o $svg -- $bin {{times}})
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
    (cd $dir && {{SAMPLED}} cargo flamegraph -c "record -F {{freq}} --call-graph fp -g" --profile flamegraph --no-default-features --features "unsafe perf" --bin bench -o $here/flamegraph-{{benchmark}}-{{ref}}.svg -- $bin {{times}})
    mv $dir/perf.data working/perf-{{benchmark}}-{{ref}}.data
    (cd working && {{SAMPLED}} cargo flamegraph -c "record -F {{freq}} --call-graph fp -g" --profile flamegraph --no-default-features --features "unsafe perf" --bin bench -o flamegraph-{{benchmark}}.svg -- {{benchmark}}.bin {{times}})
    mv working/perf.data working/perf-{{benchmark}}.data
    # `head` closing the pipe early isn't a failure.
    set +o pipefail
    for data in working/perf-{{benchmark}}-{{ref}}.data working/perf-{{benchmark}}.data; do
        echo "== $data"
        perf report -i $data --no-children -g none --sort sym --stdio 2>/dev/null | grep '%' | head -n {{top}}
    done

# `flamegraph` over HYPERFINES, or `runs` (`benchmark:times`) if named, sampling at `freq` Hz: for each run,
# working/perf-<benchmark>-<times>.data and flamegraph-<benchmark>-<times>.svg,
# then each profile's share of time by tier, and its time in each
# (tools/tiers.py): JIT code, the interpreter, specializing, contracting,
# compiling to machine code, and GC. perf runs the benchmark itself: under
# `cargo flamegraph`, samples from the run's start are the pre-exec process's,
# which perf can't resolve.
flamegraphs freq='19997' *runs:
    #!/usr/bin/env bash
    set -euo pipefail
    {{SHARED}} cargo build --profile flamegraph --no-default-features --features "unsafe perf" --bin bench -Z build-std="core,std,panic_abort"
    profiles=()
    runs="{{runs}}"
    for run in ${runs:-{{HYPERFINES}}}; do
        benchmark=${run%:*}; times=${run#*:}
        just _luac $benchmark
        # A run that fails is left out, and said so.
        if ! (cd working && {{SAMPLED}} perf record -F {{freq}} --call-graph fp -g -o perf-$benchmark-$times.data -- ../target/flamegraph/bench $benchmark.bin $times > /dev/null); then
            echo "skipped $benchmark $times: the run failed"
            continue
        fi
        # Without inlined calls' frames, which perf takes minutes to find a profile's.
        flamegraph --no-inline --perfdata working/perf-$benchmark-$times.data -o working/flamegraph-$benchmark-$times.svg > /dev/null
        profiles+=(working/perf-$benchmark-$times.data)
    done
    python3 tools/tiers.py --freq {{freq}} "${profiles[@]}"

benchmarks: (run "binarytrees") (run "life") (run "nbody")

# Interpreter: no JIT, every closure run by the specializer's interpreter loop.
INTERPRETER_FEATURES := "magic"
interpreter-compile:
    {{SHARED}} cargo build --release --no-default-features --features "{{INTERPRETER_FEATURES}}" --bin bench --bin lunacy --target-dir ./target/interpreter
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
    (cd $dir && {{SHARED}} cargo build --profile unsafe --no-default-features --features unsafe --bin bench -Z build-std="core,std,panic_abort")
    # Demangled by the `demangle` bin: objdump's -C leaves v0 symbols with enum
    # const generics mangled.
    {{SHARED}} cargo build --release --features jit_disasm --bin demangle --target-dir target/jit_disasm
    demangle=target/jit_disasm/release/demangle
    read start size < <(objdump -t $dir/target/unsafe/bench | $demangle | awk -v op='{{op}}>::__stencil::<0>' 'substr($0, length($0) - length(op) + 1) == op {print $1, $5}')
    objdump -d --no-show-raw-insn --start-address=0x$start --stop-address=$((0x$start + 0x$size)) $dir/target/unsafe/bench | $demangle | grep -E '^ +[0-9a-f]+:'

unsafe-compile:
    {{SHARED}} cargo build --profile unsafe --no-default-features --features unsafe --bin bench \
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
    {{SHARED}} cargo build --release --bin bench
    just _hyperfine {{benchmark}} {{times}} target

# `hyperfine` of the release and unsafe benches in `bins` (its `release/bench` and
# `unsafe/bench`), built already.
_hyperfine benchmark times bins:
    just _luac {{benchmark}}
    just _luajitc {{benchmark}}
    python3 tools/clock_check.py
    # A build whose run fails (e.g. past the JIT buffer's end) is still timed,
    # and left out of the history for its exit code.
    {{TIMED}} hyperfine -i --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}.md \
        --export-json working/hyperfine-{{benchmark}}-{{times}}.json \
        -n "luajit -joff" "luajit -joff bench.lua -- working/{{benchmark}}.luajit.bin {{times}}" \
        -n luajit "luajit bench.lua -- working/{{benchmark}}.luajit.bin {{times}}" \
        -n release "./{{bins}}/release/bench working/{{benchmark}}.bin {{times}}" \
        -n unsafe "./{{bins}}/unsafe/bench working/{{benchmark}}.bin {{times}}"
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
    just _tcvmc {{benchmark}}
    {{SHARED}} cargo build --release --bin bench
    # A command failing (lua5.1, lua5.5, Luau and tcvm lack the bit library) is
    # timed, and left out of the history for its exit code.
    {{TIMED}} hyperfine -i --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}.md \
        --export-json working/hyperfine-{{benchmark}}-{{times}}.json \
        -n lua5.1 "lua5.1 bench.lua -- working/{{benchmark}}.bin {{times}}" \
        -n lua5.5 "lua5.5 bench.lua -- working/{{benchmark}}.lua55.bin {{times}}" \
        -n luau "luau -O2 working/{{benchmark}}.luau -a {{times}}" \
        -n "luau --codegen" "luau -O2 --codegen working/{{benchmark}}.luau -a {{times}}" \
        -n tcvm "tcvm --file working/{{benchmark}}.tcvm.lua {{times}}" \
        -n "luajit -joff" "luajit -joff bench.lua -- working/{{benchmark}}.luajit.bin {{times}}" \
        -n luajit "luajit bench.lua -- working/{{benchmark}}.luajit.bin {{times}}" \
        -n interpreter "./target/interpreter/release/bench working/{{benchmark}}.bin {{times}}" \
        -n release "./target/release/bench working/{{benchmark}}.bin {{times}}" \
        -n unsafe "./target/unsafe/bench working/{{benchmark}}.bin {{times}}"
    python3 tools/bench_history.py record working/hyperfine-{{benchmark}}-{{times}}.json --benchmark {{benchmark}} --arg {{times}}
# Raven (https://github.com/mkeeter/raven), Matt Keeter's Uxn and Varvara
# emulator, at RAVEN_REV in target/raven: its CLI, with each of its backends,
# `--backend interpreter` (safe Rust), `tailcall` (safe Rust, tail calls) and
# `native` (x86-64 assembly).
RAVEN_REV := "14dbcbeb38cf15fa941f35095f6acf944252f4b3"
_raven:
    #!/usr/bin/env bash
    set -euo pipefail
    test -d target/raven || git clone -q https://github.com/mkeeter/raven target/raven
    git -C target/raven checkout -q --detach {{RAVEN_REV}}
    cd target/raven && {{SHARED}} cargo build -q --release -p raven-cli --features native,tailcall

# The uxn_* benchmarks run a Uxn ROM (varvara/roms) on the Lua Varvara emulator
# (varvara/), the uxn_bit_* ones on its bitwise machine, which needs the bit
# library (Lua 5.1 and 5.5 have none, so their runs fail). The emulator needs
# more JIT code than lunacy's default buffer holds: their lunacy builds get
# LUNACY_JIT_SIZE bytes.
UXN_JIT_SIZE := "16777216"

# `hyperfine-full` of a uxn_* benchmark, lunacy's builds with UXN_JIT_SIZE, and
# with `times` 1, Raven's backends running its ROM's reset vector (raven-cli
# --quit), where the ROM needs nothing past it (not bunnymark, which runs on
# frames): the same work as the benchmark's, past building the Lua machine.
hyperfine-uxn benchmark times='1': unsafe-compile interpreter-compile _raven
    #!/usr/bin/env bash
    set -euo pipefail
    b={{benchmark}}
    just _luac $b
    just _luajitc $b
    just _lua55c $b
    just _luauc $b
    {{SHARED}} cargo build --release --bin bench
    jit="LUNACY_JIT_SIZE={{UXN_JIT_SIZE}}"
    raven=()
    # uxn_<rom> or uxn_bit_<rom>.
    name=${b#uxn_}; name=${name#bit_}
    rom=working/roms/$name.rom
    if [ {{times}} = 1 ] && [ $name != bunnymark ]; then
        for backend in interpreter tailcall native; do
            raven+=(-n "raven $backend" "target/raven/target/release/raven-cli --backend $backend --quit $rom")
        done
    fi
    # As `hyperfine-full`: a command failing is timed, and left out of the history.
    {{TIMED}} hyperfine -i -N --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown working/hyperfine-$b-{{times}}.md \
        --export-json working/hyperfine-$b-{{times}}.json \
        -n lua5.1 "lua5.1 bench.lua -- working/$b.bin {{times}}" \
        -n lua5.5 "lua5.5 bench.lua -- working/$b.lua55.bin {{times}}" \
        -n luau "luau -O2 working/$b.luau -a {{times}}" \
        -n "luau --codegen" "luau -O2 --codegen working/$b.luau -a {{times}}" \
        -n "luajit -joff" "luajit -joff bench.lua -- working/$b.luajit.bin {{times}}" \
        -n luajit "luajit bench.lua -- working/$b.luajit.bin {{times}}" \
        -n interpreter "./target/interpreter/release/bench working/$b.bin {{times}}" \
        -n release "env $jit ./target/release/bench working/$b.bin {{times}}" \
        -n unsafe "env $jit ./target/unsafe/bench working/$b.bin {{times}}" \
        "${raven[@]}"
    python3 tools/bench_history.py record working/hyperfine-$b-{{times}}.json --benchmark $b --arg {{times}}

# A ROM's uxn_* and uxn_bit_* benchmarks side by side (`rom` as varvara/roms
# names it): what computing with the bit library does on each Lua that has it,
# LuaJIT, Luau and lunacy's release and unsafe builds (with UXN_JIT_SIZE), in
# working/hyperfine-uxn-bit-<rom>.md.
hyperfine-uxn-bit rom: unsafe-compile
    #!/usr/bin/env bash
    set -euo pipefail
    {{SHARED}} cargo build --release --bin bench
    commands=()
    for b in uxn_{{rom}} uxn_bit_{{rom}}; do
        just _luac $b
        just _luajitc $b
        just _luauc $b
        commands+=(-n "$b luau" "luau -O2 working/$b.luau -a 1"
            -n "$b luau --codegen" "luau -O2 --codegen working/$b.luau -a 1"
            -n "$b luajit -joff" "luajit -joff bench.lua -- working/$b.luajit.bin 1"
            -n "$b luajit" "luajit bench.lua -- working/$b.luajit.bin 1"
            -n "$b release" "env LUNACY_JIT_SIZE={{UXN_JIT_SIZE}} ./target/release/bench working/$b.bin 1"
            -n "$b unsafe" "env LUNACY_JIT_SIZE={{UXN_JIT_SIZE}} ./target/unsafe/bench working/$b.bin 1")
    done
    {{TIMED}} hyperfine -N --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown working/hyperfine-uxn-bit-{{rom}}.md \
        --export-json working/hyperfine-uxn-bit-{{rom}}.json "${commands[@]}"

# The unsafe build with `magic`, whose `jit` table's `promote` lets the Lua
# Varvara emulator specialize its loop to the virtual program counter, in
# target/magic (`unsafe-compile`'s has none: the emulator runs without).
unsafe-magic-compile:
    {{SHARED}} cargo build --profile unsafe --no-default-features --features unsafe,magic --bin bench \
        --target-dir target/magic -Z build-std="core,std,panic_abort"

# A uxn_* benchmark (`times` 1) on Raven's backends, where the ROM needs nothing
# past its reset vector (as `hyperfine-uxn`), and lunacy's unsafe build and its
# unsafe build with `magic` (`unsafe-magic-compile`).
hyperfine-uxn-promote benchmark times='1': (_hyperfine-uxn-promote benchmark times "")

# `hyperfine-uxn-promote`, and LuaJIT with and without its JIT.
hyperfine-uxn-promote-full benchmark times='1': (_hyperfine-uxn-promote benchmark times "full")

_hyperfine-uxn-promote benchmark times full: unsafe-compile unsafe-magic-compile _raven
    #!/usr/bin/env bash
    set -euo pipefail
    commands=()
    while IFS=$'\t' read -r name command; do commands+=(-n "$name" "$command"); done \
        < <(just _uxn-promote-commands {{benchmark}} {{times}} "{{full}}")
    # As `hyperfine-full`: a command failing is timed, and left out of the history.
    {{TIMED}} hyperfine -i -N --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown working/hyperfine-promote-{{benchmark}}-{{times}}.md \
        --export-json working/hyperfine-promote-{{benchmark}}-{{times}}.json "${commands[@]}"

# The implementations `hyperfine-uxn-promote` runs a uxn_* benchmark on, one
# `name<TAB>command` line each: Raven's backends, where the ROM needs nothing past
# its reset vector, LuaJIT with and without its JIT with `full`, and lunacy's
# unsafe build and its unsafe build with `magic`. Each command runs without a shell.
_uxn-promote-commands benchmark times full:
    #!/usr/bin/env bash
    set -euo pipefail
    b={{benchmark}}
    just _luac $b >&2
    name=${b#uxn_}; name=${name#bit_}
    # uxn_loop runs loop_long.tal.
    if [ $name = loop ]; then name=loop_long; fi
    rom=working/roms/$name.rom
    if [ {{times}} = 1 ] && [ $name != bunnymark ]; then
        for backend in interpreter tailcall native; do
            printf 'raven %s\t%s\n' $backend "target/raven/target/release/raven-cli --backend $backend --quit $rom"
        done
    fi
    if [ -n "{{full}}" ]; then
        just _luajitc $b >&2
        printf 'luajit -joff\t%s\n' "luajit -joff bench.lua -- working/$b.luajit.bin {{times}}"
        printf 'luajit\t%s\n' "luajit bench.lua -- working/$b.luajit.bin {{times}}"
    fi
    jit="LUNACY_JIT_SIZE={{UXN_JIT_SIZE}}"
    printf 'lunacy unsafe\t%s\n' "env $jit ./target/unsafe/bench working/$b.bin {{times}}"
    printf 'lunacy unsafe magic\t%s\n' "env $jit ./target/magic/unsafe/bench working/$b.bin {{times}}"

# What lunacy's unsafe builds, with and without `magic`, print running a uxn_*
# benchmark as `hyperfine-uxn-promote` runs them, and their exit statuses.
run-uxn-promote benchmark times='1': unsafe-compile unsafe-magic-compile
    #!/usr/bin/env bash
    set -uo pipefail
    while IFS=$'\t' read -r name command; do
        echo "== $name"
        {{SHARED}} $command; echo "== exit $?"
    done < <(just _uxn-promote-commands {{benchmark}} {{times}} "" | grep '^lunacy')

# Cycles (`perf stat`, the mean of `runs`) of each implementation
# `hyperfine-uxn-promote-full` times on a uxn_* benchmark, pinned as it pins
# them, and those cycles over `iterations`, the iterations of the ROM's loop: a
# whole run's, starting the process and compiling included. uxn_loop's loop
# runs 16 * 65535 = 1048560 times.
perf-stat-uxn-promote benchmark iterations times='1' runs='5': unsafe-compile unsafe-magic-compile _raven
    #!/usr/bin/env bash
    set -euo pipefail
    printf '%-22s %16s %12s\n' implementation cycles cycles/iter
    while IFS=$'\t' read -r name command; do
        read -ra words <<< "$command"
        cycles=$({{TIMED}} perf stat -x, -r {{runs}} -e cycles -- "${words[@]}" 2>&1 < /dev/null > /dev/null \
            | awk -F, '$3 ~ /cycles/ { print $1 }' | tail -1)
        awk -v name="$name" -v cycles="$cycles" 'BEGIN { printf "%-22s %16s %12.2f\n", name, cycles, cycles / {{iterations}} }'
    done < <(just _uxn-promote-commands {{benchmark}} {{times}} full)

# `perf-stat-uxn-promote`'s cycles on uxn_* benchmarks `long` and `short`, whose
# ROMs differ only in running their loop `iterations` more times in `long`, and
# the difference over `iterations`: one iteration's cycles, apart from starting
# the process, building the machine and compiling, which both runs do alike.
# uxn_loop runs uxn_loop_short's loop 15 * 65535 = 983025 times more.
perf-stat-uxn-slope long='uxn_loop' short='uxn_loop_short' iterations='983025' runs='5': unsafe-compile unsafe-magic-compile _raven
    #!/usr/bin/env bash
    set -euo pipefail
    cycles() {
        read -ra words <<< "$1"
        {{TIMED}} perf stat -x, -r {{runs}} -e cycles -- "${words[@]}" 2>&1 < /dev/null > /dev/null \
            | awk -F, '$3 ~ /cycles/ { print $1 }' | tail -1
    }
    printf '%-22s %16s %16s %12s\n' implementation {{long}} {{short}} cycles/iter
    while IFS=$'\t' read -r name long short; do
        l=$(cycles "$long"); s=$(cycles "$short")
        awk -v name="$name" -v l="$l" -v s="$s" 'BEGIN { printf "%-22s %16s %16s %12.2f\n", name, l, s, (l - s) / {{iterations}} }'
    done < <(paste <(just _uxn-promote-commands {{long}} 1 full) \
        <(just _uxn-promote-commands {{short}} 1 full | cut -f2))

# `perf-stat-uxn-slope` for hardware counters `events` (`perf stat`, the mean of `runs`), of the
# implementations whose names match `only` (a regex): each one's counts on `long` and `short` in
# `out`/<implementation>.{long,short}.csv, and per iteration of the loop (tools/uxn_slope.py).
# Compare runs, say with a knob set and without, with tools/uxn_slope.py over their `out`s.
perf-stat-uxn-slope-events out='working/uxn-slope' only='lunacy' long='uxn_loop' short='uxn_loop_short' iterations='983025' runs='5' events='cycles,instructions,branches,branch-misses,stalled-cycles-frontend,L1-dcache-loads,L1-dcache-load-misses,L1-icache-load-misses,iTLB-load-misses': unsafe-compile unsafe-magic-compile _raven
    #!/usr/bin/env bash
    set -euo pipefail
    rm -rf {{out}} && mkdir -p {{out}}
    while IFS=$'\t' read -r name long short; do
        [[ "$name" =~ {{only}} ]] || continue
        for rom in long short; do
            read -ra words <<< "${!rom}"
            {{TIMED}} perf stat -x, -r {{runs}} -e {{events}} -o "{{out}}/${name// /_}.$rom.csv" -- "${words[@]}" < /dev/null > /dev/null
        done
    done < <(paste <(just _uxn-promote-commands {{long}} 1 full) \
        <(just _uxn-promote-commands {{short}} 1 full | cut -f2))
    python3 tools/uxn_slope.py --iterations {{iterations}} {{out}}

# `hyperfine-uxn-promote` over the uxn_* ROMs.
hyperfines-uxn-promote: (_hyperfines-uxn-promote "hyperfine-uxn-promote")

# `hyperfine-uxn-promote-full` over the uxn_* ROMs.
hyperfines-uxn-promote-full: (_hyperfines-uxn-promote "hyperfine-uxn-promote-full")

_hyperfines-uxn-promote recipe:
    #!/usr/bin/env bash
    set -euo pipefail
    for b in uxn_fib uxn_tak uxn_mandelbrot uxn_bunnymark uxn_loop; do just {{recipe}} $b; done
    for b in uxn_fib uxn_tak uxn_mandelbrot uxn_bunnymark uxn_loop; do echo $b; tail -n +3 working/hyperfine-promote-$b-1.md; done

# Each uxn_* benchmark (which checks its own output) run once on the unsafe
# build and the unsafe build with `magic`, holding the benchmark lock shared:
# its exit status per build, for a correctness sweep.
uxn-check: unsafe-compile unsafe-magic-compile
    #!/usr/bin/env bash
    set -uo pipefail
    for b in uxn_fib uxn_tak uxn_mandelbrot uxn_bunnymark uxn_loop uxn_bit_fib uxn_bit_tak uxn_bit_mandelbrot uxn_bit_bunnymark; do
        just _luac $b > /dev/null
        printf "%-20s" $b
        for bin in target/unsafe/bench target/magic/unsafe/bench; do
            LUNACY_JIT_SIZE={{UXN_JIT_SIZE}} {{SHARED}} $bin working/$b.bin 1 > /dev/null 2>&1
            printf " %-28s %s" $bin $?
        done
        echo
    done

# `hyperfine-uxn` over UXN_HYPERFINES.
UXN_HYPERFINES := "uxn_fib:1 uxn_tak:1 uxn_mandelbrot:1 uxn_bunnymark:1 uxn_bit_fib:1 uxn_bit_tak:1 uxn_bit_mandelbrot:1 uxn_bit_bunnymark:1"
hyperfines-uxn:
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{UXN_HYPERFINES}}; do just hyperfine-uxn ${run%:*} ${run#*:}; done
    for run in {{UXN_HYPERFINES}}; do echo "${run%:*} ${run#*:}"; tail -n +3 working/hyperfine-${run%:*}-${run#*:}.md; done

# The Lua Varvara emulator's screen against Raven's snapshot tests' images:
# each ROM given input as Raven's tests give it (varvara/snapshot.lua) by
# `lua`, a Lua (`lua5.1`, `luajit`) or lunacy's release build (`lunacy`), in
# working/snapshot-<rom>.ppm, compared pixel by pixel with Raven's
# (tools/compare_snapshot.py), any differences drawn in working/snapshot-<rom>-diff.png.
SNAPSHOT_ROMS := "screen screen.auto screen.blending screen.bounds screen.pixel controller mandelbrot"
varvara-snapshots lua='lunacy': _raven
    #!/usr/bin/env bash
    set -uo pipefail
    if [ {{lua}} = lunacy ]; then {{SHARED}} cargo build --release --bin lunacy || exit 1; fi
    failed=0
    for rom in {{SNAPSHOT_ROMS}}; do
        python3 tools/bundle_bench.py --entry varvara/snapshot.lua --rom $rom > working/snapshot-$rom.lua || exit 1
        if [ {{lua}} = lunacy ]; then
            luac5.1 -o working/snapshot-$rom.bin working/snapshot-$rom.lua
            LUNACY_JIT_SIZE={{UXN_JIT_SIZE}} ./target/release/lunacy working/snapshot-$rom.bin > working/snapshot-$rom.ppm
        else
            {{lua}} working/snapshot-$rom.lua > working/snapshot-$rom.ppm
        fi
        python3 tools/compare_snapshot.py working/snapshot-$rom.ppm target/raven/raven-varvara/tests/${rom//./_}.png \
            --diff working/snapshot-$rom-diff.png || failed=1
    done
    exit $failed

# ROM `rom` (varvara/roms/<rom>.tal) run headless on the Lua Varvara emulator
# (varvara/run.lua), bundled into one chunk: working/run-<rom>.lua, compiled to
# working/run-<rom>.bin, for `lunacy` or `trace` runs of a small ROM.
uxn-bundle rom:
    python3 tools/bundle_bench.py --entry varvara/run.lua --rom {{rom}} > working/run-{{rom}}.lua
    luac5.1 -o working/run-{{rom}}.bin working/run-{{rom}}.lua

# The Lua Varvara emulator in a window (the `varvara` bin, feature
# `varvara_ui`): lunacy's release build running varvara/app.lua on ROM `rom`, a
# name in varvara/roms or a path to a .rom file. `env` is more of the bin's
# environment (`VARVARA_FRAMES`, `VARVARA_SCREENSHOT`).
varvara rom env='':
    #!/usr/bin/env bash
    set -euo pipefail
    {{SHARED}} cargo build --release --features varvara_ui --bin varvara
    python3 tools/bundle_bench.py --entry varvara/app.lua > working/varvara-app.lua
    luac5.1 -o working/varvara-app.bin working/varvara-app.lua
    rom={{rom}}
    if [ -f varvara/roms/$rom.tal ]; then
        mkdir -p working/roms
        uxnasm varvara/roms/$rom.tal working/roms/$rom.rom > /dev/null
        rom=working/roms/$rom.rom
    fi
    # GL is Mesa's, through libglvnd (see VARVARA_LIBRARY_PATH in flake.nix), by
    # EGL: a virtual display may have no GLX.
    env LD_LIBRARY_PATH=$VARVARA_LIBRARY_PATH SDL_VIDEO_FORCE_EGL=1 \
        __EGL_VENDOR_LIBRARY_DIRS=$VARVARA_MESA/share/glvnd/egl_vendor.d LIBGL_DRIVERS_PATH=$VARVARA_MESA/lib/dri \
        LUNACY_JIT_SIZE={{UXN_JIT_SIZE}} {{env}} ./target/release/varvara working/varvara-app.bin $rom

# `varvara` on a virtual display, its window after `frames` frames in
# working/varvara-<rom>.png.
varvara-screenshot rom frames='120':
    xvfb-run -a -s "-screen 0 1440x900x24" just varvara {{rom}} "VARVARA_FRAMES={{frames}} VARVARA_SCREENSHOT=working/varvara-{{rom}}.ppm"
    python3 -c 'import sys; from PIL import Image; Image.open(sys.argv[1]).save(sys.argv[2])' working/varvara-{{rom}}.ppm working/varvara-{{rom}}.png
    @echo working/varvara-{{rom}}.png

# Compare the trace-building policies of the window allocator, and streaming
# allocation, on a benchmark
# (LUNACY_TRACES; see docs/trace-register-allocation.md).
hyperfine-traces benchmark times='10' policies='streaming,single,unidirectional,bidirectional':
    just _luac {{benchmark}}
    {{SHARED}} cargo build --release --bin bench
    {{TIMED}} hyperfine --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}-traces.md -L policy {{policies}} \
        "env LUNACY_TRACES={policy} ./target/release/bench working/{{benchmark}}.bin {{times}}"
# `hyperfine-traces` over the benchmarks lunacy runs, each run enough times for
# a stable mean. life runs twice: the difference between its 1000 and 5000 runs
# is the steady-state cost of the code, the rest the upfront cost (compiling).
hyperfines-traces policies='streaming,unidirectional,bidirectional': (hyperfine-traces "life" "1000" policies) (hyperfine-traces "life" "5000" policies) (hyperfine-traces "nbody" "10" policies) (hyperfine-traces "queens" "3000" policies) (hyperfine-traces "fannkuch_redux" "150" policies)

# mimalloc's statistics for a benchmark under each trace policy, before and
# after the heap's final reset (feature `alloc_stats`), each policy's in
# target/alloc-stats-<benchmark>-<policy>.txt.
alloc-stats benchmark times='10' policies='streaming unidirectional':
    just _luac {{benchmark}}
    {{SHARED}} cargo build --release --features alloc_stats --bin bench
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
    {{SHARED}} cargo build --release --bin bench
    just unsafe-compile
    just _compare-worktree {{ref}}
    cd target/compare/{{ref}} && {{SHARED}} cargo build --release --bin bench && just unsafe-compile

# Compare this checkout's release and unsafe builds against revision `ref`'s on
# one benchmark (built as `_build-vs` builds them).
hyperfine-vs ref benchmark times='10': (_build-vs ref)
    just _luac {{benchmark}}
    # As `hyperfine`: a build whose run fails is left out of the history.
    {{TIMED}} hyperfine -i --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}-vs-{{ref}}.md \
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
    (cd target/compare/{{ref}} && {{SHARED}} cargo build --release --bin bench && just unsafe-compile)
    for run in {{HYPERFINES}}; do
        benchmark=${run%:*}; times=${run#*:}
        just _luac $benchmark
        # As `hyperfine`: a build whose run fails is left out of the history.
        {{TIMED}} hyperfine -i --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-json working/hyperfine-$benchmark-$times-{{ref}}.json \
            -n "ref release" "target/compare/{{ref}}/target/release/bench working/$benchmark.bin $times" \
            -n "ref unsafe" "target/compare/{{ref}}/target/unsafe/bench working/$benchmark.bin $times"
        python3 tools/bench_history.py record working/hyperfine-$benchmark-$times-{{ref}}.json --benchmark $benchmark --arg $times --ref {{ref}}
    done

# The benchmark history (tools/bench_history.py): each benchmark's and build's
# latest, dirty, best and first times, regressions flagged, and the charts, in
# working/history.html.
# Whether the clock is fine enough to time with: a coarse one rounds every timing to whole
# milliseconds (tools/clock_check.py). `hyperfines` won't start without it, and each benchmark it
# times checks it again, since the clock can turn coarse at any time.
clock-check:
    python3 tools/clock_check.py

bench-history:
    python3 tools/bench_history.py report
    python3 tools/bench_history.py plot

# What stops each benchmark of lua_benchmarking that HYPERFINES doesn't run:
# each run once at its scaling under LuaJIT and lunacy's release build (the
# unsafe build's panics have no message), with how each ended and its error
# (tools/bench_blockers.py); or only `benchmarks`, if named.
bench-blockers *benchmarks:
    {{SHARED}} cargo build --release --bin bench
    {{SAMPLED}} python3 tools/bench_blockers.py --exclude "{{HYPERFINES}}" {{benchmarks}}

# The latest commit's times from the benchmark history as a grouped bar chart,
# a group per benchmark, in rows of `per_row` each on its own scale, in
# working/bars.html (tools/bench_bars.py): `builds`, the implementations, in bar
# order, and `clamp`, those whose bars don't set a row's scale past 1.5 times
# the rest's highest (comma separated).
bench-bars builds='lua5.1,lua5.5,luau,luau --codegen,tcvm,luajit -joff,luajit,interpreter,release,unsafe' clamp='lua5.1,lua5.5,interpreter' per_row='5':
    python3 tools/bench_bars.py --builds "{{builds}}" --clamp "{{clamp}}" --per-row {{per_row}}
# Hardware counters (`perf stat`) for this checkout's build of `profile`
# (`release` or `unsafe`) and revision `ref`'s (built as `_build-vs` builds
# them) on one benchmark, each pinned as `hyperfine` runs it and repeated `runs`
# times.
perf-stat-vs ref benchmark times='10' runs='5' profile='unsafe' events='task-clock,cycles,instructions,branches,branch-misses,L1-icache-load-misses,iTLB-load-misses': (_build-vs ref)
    just _luac {{benchmark}}
    {{TIMED}} perf stat -r {{runs}} -e {{events}} \
        target/compare/{{ref}}/target/{{profile}}/bench working/{{benchmark}}.bin {{times}} > /dev/null
    {{TIMED}} perf stat -r {{runs}} -e {{events}} \
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
    {{SHARED}} cargo build --release --bin bench
    {{SHARED}} cargo build --release --features {{feature}} --bin bench --target-dir target/features/{{feature}}
    {{TIMED}} hyperfine --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}-{{feature}}.md \
        -n default "./target/release/bench working/{{benchmark}}.bin {{times}}" \
        -n {{feature}} "target/features/{{feature}}/release/bench working/{{benchmark}}.bin {{times}}"
hyperfine-jit benchmark:
    just _luac {{benchmark}}
    {{SHARED}} cargo build --release --bin bench
    {{TIMED}} hyperfine --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown working/hyperfine-{{benchmark}}-jit.md \
        "./target/release/bench working/{{benchmark}}.bin"
hyperfine-unsafe benchmark: unsafe-compile
    just _luac {{benchmark}}
    {{TIMED}} hyperfine --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown working/hyperfine-{{benchmark}}-unsafe.md \
        "./target/unsafe/bench working/{{benchmark}}.bin"


# The benchmarks lunacy runs, as `benchmark:times`, each run enough times for a
# stable mean; life twice, as for `hyperfines-traces`. euler14's count is the
# bound of its search.
HYPERFINES := "life:1000 life:5000 nbody:10 queens:3000 fannkuch_redux:150 euler14:1000000 nsieve_bit:10 nsieve:9 binarytrees:2 partialsums:2000000 series:2 mandelbrot:1000 mandelbrot_bit:1000 array3d:120 quicksort:300000 table_cmpsort:100000 recursive_fib:35 recursive_ack:10 spectralnorm:2 bounce:30000 md5:140 heapsort:100000 jsonlua_encode:10 deltablue:4000 havlak:1 ray:50 richards:10 collisiondetector:35"

# Which benchmarks lunacy runs (tools/bench_runs.py): each of lua_benchmarking's,
# or those named, at `fraction` of its benchinfo.json scaling, against LuaJIT, in
# lunacy's `build` (`unsafe`, or `release` for panics' messages), built first.
bench-runs fraction='0.1' build='unsafe' *benchmarks:
    {{ if build == "unsafe" { "just unsafe-compile" } else { SHARED + " cargo build --release --bin bench" } }}
    {{SAMPLED}} python3 tools/bench_runs.py --fraction {{fraction}} --build {{build}} {{benchmarks}}

# The array part stores and hash field stores each run of HYPERFINES does, by
# what the specializer knew of each stored value's type: nothing, that it's a
# number, or its type (feature `store_types`), from the run's counters.
store-types:
    #!/usr/bin/env bash
    set -euo pipefail
    {{SHARED}} cargo build --release --features store_types --bin bench --target-dir target/store_types
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
    {{TIMED}} hyperfine -i --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-json working/hyperfine-{{benchmark}}-{{times}}-interpreter.json \
        -n interpreter "./target/interpreter/release/bench working/{{benchmark}}.bin {{times}}"
    python3 tools/bench_history.py record working/hyperfine-{{benchmark}}-{{times}}-interpreter.json --benchmark {{benchmark}} --arg {{times}}

# `hyperfine-interpreter` over HYPERFINES.
hyperfines-interpreter:
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{HYPERFINES}}; do just hyperfine-interpreter ${run%:*} ${run#*:}; done

# `hyperfine` over HYPERFINES.
# The benches `hyperfines` and `jit-sizes` time and measure: built once, up front, and copied,
# with the state of the checkout they were built from (`bench_history.py state`), so the
# source can be edited while they run.
BENCH_BINS := "target/bench-snapshot"

_bench-snapshot: unsafe-compile
    mkdir -p {{BENCH_BINS}}/release {{BENCH_BINS}}/unsafe {{BENCH_BINS}}/jit_disasm
    python3 tools/bench_history.py state > {{BENCH_BINS}}/state
    {{SHARED}} cargo build --release --bin bench
    {{SHARED}} cargo build --profile unsafe --no-default-features --features "unsafe jit_disasm" --bin bench \
        --target-dir target/jit_disasm -Z build-std="core,std,panic_abort"
    cp target/release/bench {{BENCH_BINS}}/release/bench
    cp target/unsafe/bench {{BENCH_BINS}}/unsafe/bench
    cp target/jit_disasm/unsafe/bench {{BENCH_BINS}}/jit_disasm/bench

hyperfines: clock-check _bench-snapshot
    #!/usr/bin/env bash
    set -euo pipefail
    export LUNACY_BENCH_STATE={{BENCH_BINS}}/state
    for run in {{HYPERFINES}}; do just _hyperfine ${run%:*} ${run#*:} {{BENCH_BINS}}; done
    python3 tools/bench_history.py report

# The JIT code size of each benchmark of HYPERFINES run by checkout `dir`
# (this one, or revision `ref`'s compare worktree) on the benchmark as that
# checkout compiles it, from its annotated
# disassembly (as `jit-disasm` makes it), into the size history
# (tools/bench_history.py record-size). A benchmark whose run fails is left
# out, its output in working/jit-size-<benchmark>.log.
_jit-sizes dir ref='' bin='':
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
        if [ -n "{{bin}}" ]; then
            run=({{SHARED}} $PWD/{{bin}})
        else
            run=({{SHARED}} cargo run --profile unsafe --no-default-features --features "unsafe jit_disasm" --bin bench
                --target-dir ../target/jit_disasm -Z build-std="core,std,panic_abort" --)
        fi
        if (cd {{dir}}/working && "${run[@]}" $benchmark.bin $times) > working/jit-size-$benchmark.log 2>&1; then
            python3 tools/bench_history.py record-size {{dir}}/working/jit_disasm.txt --benchmark $benchmark --arg $times {{ if ref == "" { "" } else { "--ref " + ref } }} \
                || echo "skipped $benchmark $times: no size recorded"
        else
            echo "skipped $benchmark $times: its run failed (working/jit-size-$benchmark.log)"
        fi
    done

# The JIT code size of each benchmark of HYPERFINES, into the size history
# (see `_jit-sizes`).
jit-sizes: _bench-snapshot
    LUNACY_BENCH_STATE={{BENCH_BINS}}/state just _jit-sizes . "" {{BENCH_BINS}}/jit_disasm/bench

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
# Every HYPERFINES run in the unsafe build without and with `knob`, an
# environment assignment (`LUNACY_NO_INLINE=1`), and the change in each's
# median (tools/knob_table.py); a run that fails is skipped. Its json in
# working/knob/.
hyperfines-knob knob: unsafe-compile
    #!/usr/bin/env bash
    set -euo pipefail
    rm -rf working/knob && mkdir -p working/knob
    for run in {{HYPERFINES}}; do b=${run%:*}; t=${run#*:}; just _luac $b; {{TIMED}} hyperfine --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-json working/knob/$b-$t.json -n default "./target/unsafe/bench working/$b.bin $t" -n "{{knob}}" "env {{knob}} ./target/unsafe/bench working/$b.bin $t" || echo "skipped $b $t"; done
    python3 tools/knob_table.py working/knob/*.json

# Every HYPERFINES run in the unsafe build with each of `knobs`, environment
# assignments joined by commas (`LUNACY_SEAL_BUDGET=0,LUNACY_NO_GIVE_UP=1`), and
# each one's median against the first's (tools/knob_table.py); a run that fails
# is skipped. Its json in working/knobs/.
hyperfines-knobs +knobs: unsafe-compile
    #!/usr/bin/env bash
    set -euo pipefail
    rm -rf working/knobs && mkdir -p working/knobs
    for run in {{HYPERFINES}}; do
        b=${run%:*}; t=${run#*:}
        just _luac $b
        python3 tools/clock_check.py
        commands=()
        for knob in {{knobs}}; do commands+=(-n "$knob" "env ${knob//,/ } ./target/unsafe/bench working/$b.bin $t"); done
        {{TIMED}} hyperfine --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-json working/knobs/$b-$t.json "${commands[@]}" || echo "skipped $b $t"
    done
    python3 tools/knob_table.py working/knobs/*.json

# Every HYPERFINES run in the unsafe build without and with cargo feature
# `feature` (built into target/feature-<feature>), and the change in each's
# median (tools/knob_table.py); a run that fails is skipped. Its json in
# working/feature/.
hyperfines-feature feature: unsafe-compile
    #!/usr/bin/env bash
    set -euo pipefail
    {{SHARED}} cargo build --profile unsafe --no-default-features --features "unsafe {{feature}}" --bin bench \
        --target-dir target/feature-{{feature}} -Z build-std="core,std,panic_abort"
    rm -rf working/feature && mkdir -p working/feature
    for run in {{HYPERFINES}}; do b=${run%:*}; t=${run#*:}; just _luac $b; {{TIMED}} hyperfine --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-json working/feature/$b-$t.json -n default "./target/unsafe/bench working/$b.bin $t" -n "{{feature}}" "./target/feature-{{feature}}/unsafe/bench working/$b.bin $t" || echo "skipped $b $t"; done
    python3 tools/knob_table.py working/feature/*.json

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
        {{SHARED}} cargo build --release --bin bench --features "$features"
        mkdir -p target/features/$set && cp target/release/bench target/features/$set/bench
        commands+=(-n $set "target/features/$set/bench working/{{benchmark}}.bin {{times}}")
    done
    {{TIMED}} hyperfine --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown working/hyperfine-{{benchmark}}-{{times}}-features.md "${commands[@]}"

# `hyperfine-features` over HYPERFINES, then every comparison's table.
hyperfines-features +sets:
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{HYPERFINES}}; do just hyperfine-features ${run%:*} ${run#*:} {{sets}}; done
    for run in {{HYPERFINES}}; do echo "${run%:*} ${run#*:}"; tail -n +3 working/hyperfine-${run%:*}-${run#*:}-features.md; done

# This checkout's unsafe build on one benchmark with `LUNACY_JIT_PADDING` at
# each of `paddings` bytes: the same JIT code at other places in its cache
# lines, to tell a change in the code from a change in where it lands. With
# `ref`, revision `ref`'s unsafe build too (it must read the variable), each at
# every padding in the one run. Into the benchmark history as the build
# `unsafe padded`: every padding's runs pooled, and each padding's kept
# (tools/bench_history.py). With `feature`, this checkout's unsafe build with
# that cargo feature too (built into target/feature-<feature>), not recorded.
hyperfine-padding benchmark times='10' paddings='0,1,2,4,8,16' ref='' feature='':
    #!/usr/bin/env bash
    set -euo pipefail
    just unsafe-compile
    just _luac {{benchmark}}
    builds=./target/unsafe/bench
    ref="{{ref}}"
    out=working/hyperfine-{{benchmark}}-{{times}}-padding
    if [ -n "{{ref}}" ]; then
        just _compare-worktree {{ref}}
        (cd target/compare/{{ref}} && just unsafe-compile)
        builds=target/compare/{{ref}}/target/unsafe/bench,$builds
        out=$out-vs-{{ref}}
    fi
    if [ -n "{{feature}}" ]; then
        {{SHARED}} cargo build --profile unsafe --no-default-features --features "unsafe {{feature}}" --bin bench \
            --target-dir target/feature-{{feature}} -Z build-std="core,std,panic_abort"
        builds=$builds,./target/feature-{{feature}}/unsafe/bench
        out=$out-{{feature}}
    fi
    {{TIMED}} hyperfine --warmup {{WARMUP}} --max-runs {{MAX_RUNS}} --export-markdown $out.md --export-json $out.json \
        --parameter-list padding {{paddings}} --parameter-list build $builds \
        "env LUNACY_JIT_PADDING={padding} {build} working/{{benchmark}}.bin {{times}}"
    if [ -z "{{feature}}" ]; then
        python3 tools/bench_history.py record $out.json --benchmark {{benchmark}} --arg {{times}} ${ref:+--ref $ref}
    fi

# Revision `head`'s times against revision `base`'s in the benchmark history, as
# `build`, every run of each pooled: per benchmark their medians, at how many
# paddings `head` is faster, and whether their quartile boxes are apart
# (tools/bench_history.py `vs`).
bench-vs base head build='unsafe padded':
    python3 tools/bench_history.py vs {{base}} {{head}} --build "{{build}}"

# `hyperfine-padding` over HYPERFINES, then the JIT code size of each
# benchmark into the size history: this checkout's (`jit-sizes`), and with
# `ref` revision `ref`'s (`jit-size-rev`).
hyperfines-padding paddings='0,1,2,4,8,16' ref='':
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{HYPERFINES}}; do just hyperfine-padding ${run%:*} ${run#*:} {{paddings}} {{ref}}; done
    just jit-sizes
    if [ -n "{{ref}}" ]; then just jit-size-rev {{ref}}; fi

# `hyperfine-vs ref` over HYPERFINES, then every comparison's table.
hyperfines-vs ref:
    #!/usr/bin/env bash
    set -euo pipefail
    for run in {{HYPERFINES}}; do just hyperfine-vs {{ref}} ${run%:*} ${run#*:}; done
    for run in {{HYPERFINES}}; do tail -n 4 working/hyperfine-${run%:*}-${run#*:}-vs-{{ref}}.md; done
    python3 tools/bench_history.py report

all: test benchmarks (hyperfine "binarytrees")

# Experiment: stencil holes as LLVM patchpoints instead of RIP-relative loads.
# experiments/patchpoint/hole.ll wraps `llvm.experimental.patchpoint.i64` (and
# a stackmap) in plain functions, made ThinLTO bitcode (with a summary: plain
# bitcode is a separate full-LTO partition, which ThinLTO never inlines from)
# by the LLVM release rustc is built on; experiments/patchpoint/main.rs calls
# them and is built with `-C linker-plugin-lto` and linked by rustc's own lld,
# so LTO inlines the wrappers into the Rust callers. `.llvm_stackmaps` needs
# keeping from section GC, and its absolute relocations in a read-only section
# need `-z notext` under PIE. Built with rustc directly, not as a cargo bin, so
# the crate's build never needs the bitcode. Writes the binary, LTO's
# intermediate files, each `ex_*` function's disassembly and the stackmap to
# target/patchpoint/.
patchpoint-experiment:
    #!/usr/bin/env bash
    set -euo pipefail
    out=target/patchpoint
    mkdir -p $out
    llvm=$(nix build --no-link --print-out-paths --inputs-from . nixpkgs#llvmPackages_23.llvm)/bin
    $llvm/llvm-as --version | grep version
    rustc --version --verbose | grep LLVM
    $llvm/opt --thinlto-bc experiments/patchpoint/hole.ll -o $out/hole.bc
    {{SHARED}} rustc --edition 2024 -C opt-level=3 -C codegen-units=1 -C panic=abort -C target-cpu=native \
        -C linker-plugin-lto -C linker-flavor=gnu-lld-cc -Z unstable-options -C link-self-contained=+linker \
        -C link-arg=$out/hole.bc -C link-arg=-Wl,--save-temps -C link-arg=-Wl,--no-gc-sections -C link-arg=-Wl,-z,notext -o $out/patchpoint_experiment experiments/patchpoint/main.rs
    {{SHARED}} $out/patchpoint_experiment
    syms=$($llvm/llvm-nm $out/patchpoint_experiment | awk '$3 ~ /^(ex_|pp_|sm_)/ {print $3}' | sort)
    echo "symbols: $syms"
    for s in $(echo "$syms" | grep '^ex_'); do
        $llvm/llvm-objdump -d -M intel --disassemble-symbols=$s $out/patchpoint_experiment | sed -n '/^[0-9a-f]* </,$p'
    done | tee $out/disasm.txt
    $llvm/llvm-readobj --stackmap $out/patchpoint_experiment | tee $out/stackmap.txt
    $llvm/llvm-objdump -s -j .lunacy_imm_holes $out/patchpoint_experiment || true

# A hole declared as the stencils declare theirs (experiments/weak_hole), built
# as a PIE (as lunacy is), non-PIE with relocation-model=static, and that with
# --emit-relocs: each one's code for `x - hole` and `x & hole`, and the
# relocations, dynamic and static, at or into those functions.
weak-hole-experiment:
    #!/usr/bin/env bash
    set -euo pipefail
    out=target/weak_hole
    mkdir -p $out
    build() {
        name=$1; shift
        {{SHARED}} rustc --edition 2024 -C opt-level=3 -C panic=abort -C codegen-units=1 "$@" \
            -o $out/$name experiments/weak_hole/main.rs
        echo "=== $name: $* ; runs: $($out/$name)"
        objdump -d -M intel --no-show-raw-insn $out/$name | awk '/<ex_(sub|and)_hole>:/{p=1} p&&/^$/{p=0} p'
        lo=$(nm $out/$name | awk '$3=="ex_sub_hole"{print $1}')
        echo "--- relocations naming the hole, or within ex_*:"
        readelf -rW $out/$name | grep -E "__lunacy_hole1|^$lo" || echo "(none)"
    }
    build pie
    build static -C relocation-model=static
    build static-emit-relocs -C relocation-model=static -C link-arg=-Wl,--emit-relocs

# Holes as `!absolute_symbol` globals (experiments/absolute_hole): an IR module
# declaring them, with accessors cross-language ThinLTO inlines into the Rust
# using them, linked as a PIE (as `patchpoint-experiment` links): each
# function's code, and the relocations at or into them and naming the holes.
# `link` is extra linker arguments, comma separated, e.g. `-z,notext`.
absolute-hole-experiment link='':
    #!/usr/bin/env bash
    set -euo pipefail
    out=target/absolute_hole
    mkdir -p $out
    llvm=$(nix build --no-link --print-out-paths --inputs-from . nixpkgs#llvmPackages_23.llvm)/bin
    $llvm/opt --thinlto-bc experiments/absolute_hole/hole.ll -o $out/hole.bc
    extra=()
    if [ -n "{{link}}" ]; then extra=(-C "link-arg=-Wl,{{link}}"); fi
    {{SHARED}} rustc --edition 2024 -C opt-level=3 -C codegen-units=1 -C panic=abort -C target-cpu=native \
        -C linker-plugin-lto -C linker-flavor=gnu-lld-cc -Z unstable-options -C link-self-contained=+linker \
        -C link-arg=$out/hole.bc -C link-arg=-Wl,--save-temps "${extra[@]}" \
        -o $out/absolute_hole experiments/absolute_hole/main.rs
    echo "runs: $({{SHARED}} $out/absolute_hole)"
    for s in ex_sub_hole ex_and_hole ex_add_small_hole ex_cmp_hole; do
        $llvm/llvm-objdump -d -M intel --disassemble-symbols=$s $out/absolute_hole | sed -n '/^[0-9a-f]* </,$p'
    done | tee $out/disasm.txt
    echo "--- relocations naming the holes:"
    readelf -rW $out/absolute_hole | grep -E "__lunacy_abs_hole" || echo "(none)"

# `llc` alone on experiments/absolute_hole/isel.ll, as PIC: which operations
# take an `!absolute_symbol` hole as their immediate operand.
absolute-hole-isel:
    #!/usr/bin/env bash
    set -euo pipefail
    llvm=$(nix build --no-link --print-out-paths --inputs-from . nixpkgs#llvmPackages_23.llvm)/bin
    $llvm/llc -O3 -relocation-model=pic -x86-asm-syntax=intel experiments/absolute_hole/isel.ll -o - \
        | grep -vE '^\s*(\.|#)' | grep -vE '^\s*$'
