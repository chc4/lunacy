#!/usr/bin/env python3
"""A golden test's expected output, from LuaJIT.

Runs each lua_tests file through `luajit` with its `__jit` lines (lunacy's
debugging key, which LuaJIT rejects) and its `-- EXPECT:` lines left out, and
prints what it prints; with `--write`, replaces the file's `-- EXPECT:` lines
with it. Run in the devshell (`nix develop`), which has `luajit`.
"""
import argparse
import os
import subprocess
import sys
import tempfile


def expected(path):
    with open(path) as f:
        lines = f.read().splitlines()
    body = [line for line in lines if '__jit' not in line and not line.startswith('-- EXPECT:')]
    with tempfile.NamedTemporaryFile('w', suffix='.lua', dir=os.path.dirname(os.path.abspath(path)), delete=False) as f:
        f.write('\n'.join(body) + '\n')
        stripped = f.name
    try:
        run = subprocess.run(['luajit', stripped], capture_output=True, text=True)
    finally:
        os.unlink(stripped)
    if run.returncode != 0:
        sys.exit(f'{path}: luajit failed:\n{run.stderr}')
    return lines, run.stdout.splitlines()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('files', nargs='+')
    ap.add_argument('--write', action='store_true', help="replace the files' -- EXPECT: lines")
    args = ap.parse_args()
    for path in args.files:
        lines, out = expected(path)
        if not args.write:
            print(f'== {path}')
            print('\n'.join(out))
            continue
        kept = [line for line in lines if not line.startswith('-- EXPECT:')]
        while kept and not kept[-1].strip():
            kept.pop()
        with open(path, 'w') as f:
            f.write('\n'.join(kept + [f'-- EXPECT: {line}' for line in out]) + '\n')
        print(f'{path}: {len(out)} expected lines')


if __name__ == '__main__':
    sys.exit(main())
