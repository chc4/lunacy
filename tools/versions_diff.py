#!/usr/bin/env python3
"""Live versions per point (`point_versions`, tools/trace_sql.py) in two traces, where they differ.

    tools/versions_diff.py BEFORE.fxt AFTER.fxt

Each line: the point's function line and pc, its live versions before and after, and those made.
"""
import argparse
import subprocess
import sys


def points(trace):
    out = subprocess.run([sys.executable, 'tools/trace_sql.py', '--trace', trace,
                          'SELECT line, pc, live, created FROM point_versions'],
                         capture_output=True, text=True, check=True).stdout.splitlines()
    rows = {}
    for row in out[1:]:
        fields = row.split()
        if len(fields) == 4 and fields[0].isdigit():
            rows[(int(fields[0]), int(fields[1]))] = (int(fields[2]), int(fields[3]))
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('before')
    ap.add_argument('after')
    args = ap.parse_args()
    before, after = points(args.before), points(args.after)
    print(f"{'line':>5} {'pc':>4}  {'live':>9}  {'made':>9}")
    for key in sorted(set(before) | set(after)):
        b, a = before.get(key, (0, 0)), after.get(key, (0, 0))
        if b[0] != a[0]:
            print(f"{key[0]:>5} {key[1]:>4}  {b[0]:>4}->{a[0]:<4}  {b[1]:>4}->{a[1]:<4}")


if __name__ == '__main__':
    main()
