#!/usr/bin/env python3
"""Which benchmarks lunacy runs: each of lua_benchmarking's (or those named), at a
fraction of its benchinfo.json scaling, compiled by `just _luac` and `_luajitc`,
run by lunacy's release build and by LuaJIT. Per benchmark, each run's time or
how it failed (lunacy's panic message), and whether their outputs agree.

    bench_runs.py [--fraction F] [--timeout S] [benchmark ...]
"""
import argparse
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BENCHES = ROOT / "lua_benchmarking"


def run(cmd, timeout):
    start = time.monotonic()
    try:
        p = subprocess.run(cmd, cwd=ROOT, capture_output=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, f"timed out after {timeout}s", b""
    elapsed = time.monotonic() - start
    if p.returncode != 0:
        err = p.stderr.decode(errors="replace")
        m = re.search(r"panicked at [^\n]*\n([^\n]*)", err)
        why = m.group(1) if m else (err.strip().splitlines() or [f"exit {p.returncode}"])[-1]
        return None, why[:160], p.stdout
    return elapsed, None, p.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("benchmarks", nargs="*")
    parser.add_argument("--fraction", type=float, default=0.1)
    parser.add_argument("--timeout", type=float, default=60)
    args = parser.parse_args()

    # benchinfo.json has trailing commas.
    info = json.loads(re.sub(r",(\s*[}\]])", r"\1", (BENCHES / "benchinfo.json").read_text()))
    scaling = info["scaling"]
    names = args.benchmarks or sorted(p.name for p in (BENCHES / "benchmarks").iterdir() if (p / "bench.lua").is_file())
    subprocess.run(["cargo", "build", "--release", "--bin", "bench"], cwd=ROOT, check=True, capture_output=True)
    for name in names:
        n = max(1, int(scaling.get(name, 1) * args.fraction))
        compiled = all(subprocess.run(["just", recipe, name], cwd=ROOT, capture_output=True).returncode == 0
                       for recipe in ("_luac", "_luajitc"))
        if not compiled:
            print(f"{name} {n}: doesn't compile")
            continue
        ours, our_err, our_out = run(["./target/release/bench", f"working/{name}.bin", str(n)], args.timeout)
        theirs, their_err, their_out = run(["luajit", "bench.lua", "--", f"working/{name}.luajit.bin", str(n)], args.timeout)
        show = lambda t, e: f"{t:.2f}s" if e is None else f"failed: {e}"
        # lunacy's report of its run isn't the benchmark's output.
        ours_only = re.compile(rb"^(> starting benchmark|counters after run .*)\n", re.M)
        agree = "" if our_err or their_err else ("  outputs agree" if ours_only.sub(b"", our_out) == their_out else "  OUTPUTS DIFFER")
        print(f"{name} {n}: lunacy {show(ours, our_err)}  luajit {show(theirs, their_err)}{agree}", flush=True)


if __name__ == "__main__":
    sys.exit(main())
