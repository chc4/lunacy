#!/usr/bin/env python3
"""What stops each benchmark of lua_benchmarking that HYPERFINES doesn't run:
each is bundled and compiled as `just _luac` does, run once at its scaling in
lua_benchmarking/benchinfo.json under LuaJIT (which has every library the
suite uses) and under lunacy's release build (target/release/bench: the unsafe
build aborts on a panic without its message), and reported with how each run
ended and each's error (a panic's message, or Lua's error line). A run past
`--timeout` still running is reported as such.

    tools/bench_blockers.py [--exclude "life:1000 nbody:10 ..."] [--timeout 60] [BENCHMARK...]
(in the devshell, after `cargo build --release --bin bench`; `just bench-blockers`)
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SUITE = ROOT / 'lua_benchmarking' / 'benchmarks'


def run(cmd, timeout):
    try:
        r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=timeout)
        return r.returncode, r.stdout, r.stderr
    except subprocess.TimeoutExpired:
        return 'timeout', '', ''


def lua_error(stderr):
    lines = [l for l in stderr.splitlines() if l.strip()]
    return lines[0].split(': ', 1)[-1] if lines else ''


def first_error(stdout, stderr):
    lines = stderr.splitlines()
    for i, line in enumerate(lines):
        if 'panicked at' in line:
            return (lines[i + 1] if i + 1 < len(lines) else line).strip()
    for line in reversed(lines):
        if line.strip() and not line.startswith(('note:', 'stack backtrace')):
            return line.strip()
    out = stdout.strip().splitlines()
    return out[-1] if out else ''


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('benchmarks', nargs='*')
    ap.add_argument('--exclude', default='', help='HYPERFINES: benchmark:arg pairs not to check')
    ap.add_argument('--timeout', type=int, default=60)
    args = ap.parse_args()

    # benchinfo.json has trailing commas, which JSON doesn't allow.
    info = json.loads(re.sub(r',(\s*[}\]])', r'\1', (ROOT / 'lua_benchmarking' / 'benchinfo.json').read_text()))
    scaling = info['scaling']
    excluded = {pair.split(':')[0] for pair in args.exclude.split()}
    names = args.benchmarks or sorted(p.name for p in SUITE.iterdir() if p.is_dir() and p.name not in excluded)
    for name in names:
        built, _, err = run(['just', '_luac', name], args.timeout)
        if built != 0:
            print(f'{name:22} build failed: {first_error("", err)}')
            continue
        n = str(scaling.get(name, 1))
        lua, _, lua_err = run(['luajit', 'bench.lua', '--', f'working/{name}.lua', n], args.timeout)
        code, out, err = run(['target/release/bench', f'working/{name}.bin', n], args.timeout)
        status = lambda c: 'ok' if c == 0 else ('still running' if c == 'timeout' else f'exit {c}')
        lua_status = status(lua) + ('' if lua in (0, 'timeout') else f' ({lua_error(lua_err)[:70]})')
        print(f'{name:18} ({n}) luajit {lua_status}\n{"":18} lunacy {status(code)} {"" if code in (0, "timeout") else first_error(out, err)}', flush=True)


if __name__ == '__main__':
    main()
