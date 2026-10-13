#!/usr/bin/env python3
"""Two revisions' JIT code sizes per benchmark, from the size history
(bench/jit_sizes.jsonl, as `just jit-sizes` and `just jit-size-rev` record it): each
one's latest bytes and sections, and the change. A revision is a commit's prefix; a
dirty run of it counts as it.

    tools/jit_sizes_vs.py BASE HEAD
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main(base, head):
    latest = {}
    for line in (ROOT / 'bench/jit_sizes.jsonl').read_text().splitlines():
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            continue
        for rev in (base, head):
            if r['commit'].startswith(rev):
                key = (r['benchmark'], r['arg'], rev)
                if key not in latest or r['date'] > latest[key]['date']:
                    latest[key] = r
    names = sorted({(b, a) for b, a, _ in latest})
    total = [0, 0]
    for benchmark, arg in names:
        old, new = latest.get((benchmark, arg, base)), latest.get((benchmark, arg, head))
        if not old or not new:
            continue
        total[0] += old['bytes']
        total[1] += new['bytes']
        change = 100 * (new['bytes'] / old['bytes'] - 1)
        print(f"{benchmark + ' ' + arg:24} {old['bytes']:7d} -> {new['bytes']:7d} {change:+6.1f}%"
              f"  sections {old.get('sections')} -> {new.get('sections')}")
    if total[0]:
        print(f"{'total':24} {total[0]:7d} -> {total[1]:7d} {100 * (total[1] / total[0] - 1):+6.1f}%")


if __name__ == '__main__':
    main(*sys.argv[1:3])
