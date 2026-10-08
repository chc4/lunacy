#!/usr/bin/env python3
"""Count the upvalue loads and function guards in each function's versions,
from residual graph dumps (`func_<line>.dot`, feature `graph`, as `just
window-runs` writes them): per function, its versioned blocks, how many of its
residuals are each kind, and the same weighted by how often each block was
entered. A function guard is a `guard(N, func)` and the identity guard after it
(`native_guard`, `lua_guard`); an upvalue load is a `GetUpval`, a `HeldUpval` (a
move from a slot known to hold the upvalue) or a `NativeUpval` (a native the
context knows the upvalue holds, as a constant). With two directories, a column
for each.

    tools/upvalue_guards.py DIR [DIR_B] [--lines 76,80]
"""
import argparse
import re
from collections import Counter
from pathlib import Path

# A versioned block's node label: `"<id> x<entered> | { PC: SubPc(..)\n<context> | r1| r2 }"`.
NODE = re.compile(r'label="(\d+) x(\d+) \| \{ PC: SubPc\(\d+, \d+\)\\ncontext\(.*?\]\) \| (.*?) \}"')
KINDS = {
    'func guard': re.compile(r'^guard\(\d+, func\)$'),
    'native_guard': re.compile(r'^native_guard\('),
    'lua_guard': re.compile(r'^lua_guard\('),
    'GetUpval': re.compile(r'^window\(GetUpval\b'),
    'HeldUpval': re.compile(r'^window\(HeldUpval\b'),
    'NativeUpval': re.compile(r'^window\(NativeUpval\b'),
}


def counts(path):
    """(versioned blocks, Counter of kinds, Counter of kinds weighted by entries)."""
    blocks, static, dynamic = 0, Counter(), Counter()
    for match in NODE.finditer(path.read_text()):
        blocks += 1
        entered = int(match.group(2))
        for residual in match.group(3).split('|'):
            residual = residual.strip()
            for kind, pattern in KINDS.items():
                if pattern.search(residual):
                    static[kind] += 1
                    dynamic[kind] += entered
    return blocks, static, dynamic


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('dirs', nargs='+')
    ap.add_argument('--lines', default='', help='comma-separated function lines (func_<line>.dot)')
    args = ap.parse_args()
    dirs = [Path(d) for d in args.dirs]
    lines = [int(l) for l in args.lines.split(',')] if args.lines else sorted(
        {int(re.search(r'\d+', p.name).group()) for d in dirs for p in d.glob('func_*.dot')})
    for line in lines:
        runs = [counts(d / f'func_{line}.dot') if (d / f'func_{line}.dot').exists() else None for d in dirs]
        print(f'func_{line}: versioned blocks ' + ' / '.join('-' if r is None else str(r[0]) for r in runs))
        for kind in KINDS:
            cells = ['-' if r is None else f'{r[1][kind]} (x{r[2][kind]})' for r in runs]
            if any(r is not None and r[1][kind] for r in runs):
                print(f'  {kind:<13} ' + '  /  '.join(cells))


if __name__ == '__main__':
    main()
