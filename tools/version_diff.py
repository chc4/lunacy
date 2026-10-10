#!/usr/bin/env python3
"""How the versions compiled at one point differ: each `spec_version` of the
function at `line` and pc `pc` (with `like`, only those whose context contains
it, e.g. a green), in order, with how its context differs from the first's,
token by token. From a trace (`just trace`).

    tools/version_diff.py LINE PC [--like TEXT] [--outcome new] [--trace working/lunacy.fxt]
"""
import argparse
import difflib
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from trace_sql import connect


def tokens(context):
    """A context split where its parts separate, so a diff names the part that changed."""
    return re.split(r'(?<=[,\])}]) ', context)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('line', type=int)
    ap.add_argument('pc', type=int)
    ap.add_argument('--like', default='')
    ap.add_argument('--outcome', default='new')
    ap.add_argument('--trace', default='working/lunacy.fxt')
    args = ap.parse_args()
    like = args.like.replace("'", "''")
    rows = list(connect(args.trace).query(
        f"select ts, block, outcome, context from spec_version where line = {args.line} and pc = {args.pc} "
        f"and outcome = '{args.outcome}' and context like '%{like}%' order by ts"))
    if not rows:
        print('(no versions)')
        return
    first = tokens(rows[0].context)
    for r in rows:
        diff = [d for d in difflib.ndiff(first, tokens(r.context)) if d[0] in '+-']
        print(f'{r.ts / 1e9:9.4f}s block {r.block}: ' + (' | '.join(diff) if diff else '(the first)'))


if __name__ == '__main__':
    main()
