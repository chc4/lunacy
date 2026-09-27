#!/usr/bin/env python3
"""Total the samples of `perf report` symbol listings by what ran them.

Reads `perf report --no-children -g none --sort sym --stdio` output (one file
per profile, as `just flamegraph-vs` saves them) and totals the JIT's blocks by
the Lua line their perf map names them with (`jit_block_<id> :<line>`), beside
the native symbols, side by side, with the difference between the first two.

With `--counts`, it compares sample counts (`perf report -n`'s column) rather
than percentages, as profiles of runs of different lengths need: with a fixed
sampling period (`perf record -e instructions -c N`) each count is N events.
"""
import argparse
import re
import sys
from collections import defaultdict

LINE = re.compile(r'^\s*([\d.]+)%\s+(?:(\d+)\s+)?\[\.\]\s+(.*?)\s*$')
JIT = re.compile(r'^jit_block_\d+ :(\d+)$')


def totals(path, counts):
    out = defaultdict(float)
    for line in open(path):
        m = LINE.match(line)
        if not m:
            continue
        if counts and m.group(2) is None:
            sys.exit(f'{path}: no sample counts (perf report -n)')
        value, sym = float(m.group(2) if counts else m.group(1)), m.group(3)
        jit = JIT.match(sym)
        out[f'JIT line {jit.group(1)}' if jit else sym] += value
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('reports', nargs='+', help='perf report outputs')
    ap.add_argument('--top', type=int, default=30, help='rows to show')
    ap.add_argument('--counts', action='store_true', help="compare sample counts, not percentages")
    args = ap.parse_args()
    all_totals = [totals(p, args.counts) for p in args.reports]
    keys = set().union(*all_totals)
    def delta(k):
        return all_totals[-1].get(k, 0) - all_totals[0].get(k, 0) if len(all_totals) > 1 else 0
    rows = sorted(keys, key=lambda k: -max(t.get(k, 0) for t in all_totals))[:args.top]
    name_width = min(90, max(len(k) for k in rows))
    header = ''.join(f'{p.split("/")[-1][:18]:>20}' for p in args.reports)
    print(f'{"":{name_width}}{header}{"delta":>10}' if len(all_totals) > 1 else f'{"":{name_width}}{header}')
    for k in rows:
        unit = '' if args.counts else '%'
        cols = ''.join(f'{t.get(k, 0):>19.2f}{unit}' for t in all_totals)
        tail = f'{delta(k):>+9.2f}{unit}' if len(all_totals) > 1 else ''
        print(f'{k[:name_width]:{name_width}}{cols}{tail}')
    jit = [sum(v for k, v in t.items() if k.startswith('JIT line')) for t in all_totals]
    unit = '' if args.counts else '%'
    print(f'{"all JIT code":{name_width}}' + ''.join(f'{v:>19.2f}{unit}' for v in jit))


if __name__ == '__main__':
    sys.exit(main())
