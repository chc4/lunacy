#!/usr/bin/env python3
"""A benchmark's hash keys and versions in two traces (`just hash-keys-vs`): per
trace, its versions, the widest hash key array any version has (the witnesses
its function's frames need), the live hash keys a version has on average, and
how many of its JIT-compiled blocks' code initializes a witness (`HrefInit`)
or loads through one (`GetTableHref`), side by side.

    tools/hash_key_stats.py BENCHMARK BASE.fxt HEAD.fxt
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from trace_sql import connect

HKEY = re.compile(r'hkey\(')


def stats(trace):
    tp = connect(trace)
    versions = list(tp.query("select context from spec_version where outcome in ('new', 'joined-new')"))
    widths, live = [], []
    for v in versions:
        ctx = v.context or ''
        hkeys = ctx[ctx.find('hkeys:'):ctx.find('fragile')] if 'hkeys:' in ctx else ''
        entries = hkeys.split('hkey(')[1:]
        widths.append(len(entries))
        # A free index prints as `hkey(<field>, free)`.
        live.append(sum(1 for e in entries if not re.match(r'[^,]*, free\b', e)))
    blocks = list(tp.query("select code from block_summary where compiled = 1"))
    return {
        'versions': len(versions),
        'widest hkeys': max(widths, default=0),
        'mean live hkeys': sum(live) / len(live) if live else 0,
        'compiled blocks': len(blocks),
        'with HrefInit': sum('HrefInit' in (b.code or '') for b in blocks),
        'with GetTableHref': sum('GetTableHref' in (b.code or '') for b in blocks),
    }


def main():
    benchmark, base, head = sys.argv[1:4]
    a, b = stats(base), stats(head)
    print(f'== {benchmark}')
    for k in a:
        fmt = (lambda x: f'{x:8.2f}') if isinstance(a[k], float) else (lambda x: f'{x:8}')
        print(f'  {k:18} {fmt(a[k])} -> {fmt(b[k])}')


if __name__ == '__main__':
    main()
