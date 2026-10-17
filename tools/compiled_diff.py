#!/usr/bin/env python3
"""Compiled code per point (`block_summary`, tools/trace_sql.py) in two traces, where it differs.

    tools/compiled_diff.py BEFORE.fxt AFTER.fxt [--code]

Each line: the point's function line and pc, its compiled blocks and their residuals before and
after. With --code, each differing point's compiled blocks' code, before then after.
"""
import argparse
import subprocess
import sys
from collections import defaultdict


def blocks(trace):
    out = subprocess.run([sys.executable, 'tools/trace_sql.py', '--trace', trace,
                          "SELECT line, pc, residuals, block, code FROM block_summary WHERE compiled"],
                         capture_output=True, text=True, check=True).stdout.splitlines()
    points = defaultdict(list)
    for row in out[1:]:
        fields = row.split(None, 4)
        if len(fields) >= 4 and fields[0].isdigit():
            points[(int(fields[0]), int(fields[1]))].append((int(fields[2]), int(fields[3]), fields[4] if len(fields) > 4 else ''))
    return points


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('before')
    ap.add_argument('after')
    ap.add_argument('--code', action='store_true', help="print each differing point's compiled code")
    args = ap.parse_args()
    before, after = blocks(args.before), blocks(args.after)
    print(f"{'line':>5} {'pc':>4}  {'blocks':>9}  {'residuals':>11}")
    totals = [0, 0, 0, 0]
    for key in sorted(set(before) | set(after)):
        b, a = before.get(key, []), after.get(key, [])
        counts = (len(b), sum(r for r, _, _ in b), len(a), sum(r for r, _, _ in a))
        totals = [t + c for t, c in zip(totals, counts)]
        if counts[:2] != counts[2:]:
            print(f"{key[0]:>5} {key[1]:>4}  {counts[0]:>4}->{counts[2]:<4}  {counts[1]:>5}->{counts[3]:<5}")
            if args.code:
                for label, side in (('-', b), ('+', a)):
                    for _, block, code in side:
                        print(f"        {label} {block}: {code}")
    print(f"{'all':>10}  {totals[0]:>4}->{totals[2]:<4}  {totals[1]:>5}->{totals[3]:<5}")


if __name__ == '__main__':
    main()
