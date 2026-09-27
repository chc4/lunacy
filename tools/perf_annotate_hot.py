#!/usr/bin/env python3
"""A function's sampled instructions from a profile, in address order, with
their share of its samples and the source line each came from, so a function's
hot path reads as a path: `perf annotate` of `symbol` in `perf.data`.

    tools/perf_annotate_hot.py PERF_DATA SYMBOL [--min PERCENT]

(in the devshell, which has perf)
"""
import argparse
import re
import subprocess
import sys

INST = re.compile(r'^\s+([\d.]+) :\s+([0-9a-f]+):\s+(.*)$')
SOURCE = re.compile(r'^\s+:\s+\d+\s+(.*\S)\s*$')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('data')
    ap.add_argument('symbol')
    ap.add_argument('--min', type=float, default=0.3, help='least share of the samples an instruction shows with')
    args = ap.parse_args()
    out = subprocess.run(['perf', 'annotate', '-i', args.data, '--stdio', '-l', '-s', args.symbol],
                         capture_output=True, text=True).stdout
    source, shown, total = '', 0, 0.0
    for line in out.splitlines():
        s = SOURCE.match(line)
        if s:
            source = s.group(1)
            continue
        m = INST.match(line)
        if not m:
            continue
        pct = float(m.group(1))
        total += pct
        if pct >= args.min:
            shown += 1
            print(f'{pct:5.2f} {m.group(2)} {m.group(3)[:70]:70} {source[:60]}')
    print(f'{shown} instructions shown, of {total:.1f}% sampled')
    return 0


if __name__ == '__main__':
    sys.exit(main())
