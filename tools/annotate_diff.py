#!/usr/bin/env python3
"""Compare two `perf annotate --stdio` listings of one function, instruction by
instruction.

The function's code must be the same in both (as when only its callers or data
changed): instructions are matched by offset from the function's start. Each
listing's percentages are scaled to sample counts by the symbol's total samples
(`perf report -n`), so runs of different lengths compare; with a fixed period
(`perf record -e instructions -c N`) a count is N events. Prints the
instructions whose counts differ most.

    tools/annotate_diff.py OLD.txt OLD_SAMPLES NEW.txt NEW_SAMPLES [--top N]
"""
import argparse
import re
import sys

LINE = re.compile(r'^\s+([\d.]+) :\s+([0-9a-f]+):\s+(.*)$')


def samples(path, total):
    rows = [(float(m.group(1)), int(m.group(2), 16), m.group(3)) for m in map(LINE.match, open(path)) if m]
    if not rows:
        sys.exit(f'{path}: no annotated instructions')
    start = min(addr for _, addr, _ in rows)
    return {addr - start: (pct * total / 100, inst) for pct, addr, inst in rows}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('old')
    ap.add_argument('old_samples', type=float)
    ap.add_argument('new')
    ap.add_argument('new_samples', type=float)
    ap.add_argument('--top', type=int, default=20)
    args = ap.parse_args()
    old, new = samples(args.old, args.old_samples), samples(args.new, args.new_samples)
    rows = []
    for offset in sorted(set(old) | set(new)):
        o, n = old.get(offset, (0, '')), new.get(offset, (0, ''))
        rows.append((n[0] - o[0], offset, o[0], n[0], (n[1] or o[1])[:70]))
    for delta, offset, o, n, inst in sorted(rows, key=lambda r: -abs(r[0]))[:args.top]:
        print(f'+{offset:#06x} {o:8.1f} {n:8.1f} {delta:+8.1f}  {inst}')


if __name__ == '__main__':
    sys.exit(main())
