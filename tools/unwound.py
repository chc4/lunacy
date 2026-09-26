#!/usr/bin/env python3
"""How much of a profile perf unwound: the share of samples whose call chain
reaches `main` (its "children" share in `perf report --children`), and the
self share of JIT code (`jit_block_*`, named by the `perf` feature's map file).
Every sample of a benchmark runs under `main`, so the samples not reaching it
are ones perf could not unwind that far.

    tools/unwound.py [perf.data]

(`perf` must be on PATH, as in `nix develop`.)
"""
import re
import subprocess
import sys

ROW = re.compile(r'^\s+([\d.]+)%\s+([\d.]+)%\s+\[.\]\s+(.*?)\s*$')


def main():
    data = sys.argv[1] if len(sys.argv) > 1 else 'perf.data'
    out = subprocess.run(['perf', 'report', '-i', data, '--children', '--sort', 'symbol', '--stdio', '-g', 'none'],
                         capture_output=True, text=True, check=True).stdout
    reached = jit = 0.0
    for line in out.splitlines():
        m = ROW.match(line)
        if not m:
            continue
        # The symbol, before the columns perf pads the row with.
        children, own, symbol = float(m.group(1)), float(m.group(2)), re.split(r'\s{2,}', m.group(3))[0]
        if symbol == 'main':
            reached = children
        if symbol.startswith('jit_block'):
            jit += own
    print('samples reaching main: %.1f%%' % reached)
    print('samples in JIT code:   %.1f%%' % jit)


if __name__ == '__main__':
    main()
