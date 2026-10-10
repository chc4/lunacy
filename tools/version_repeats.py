#!/usr/bin/env python3
"""Whether versions compiled late in a run are new contexts or old ones again:
each version a function compiles (`spec_version` with outcome `new`) in each
time slice of the run, and how many of them have a context an earlier version
at the same point already had (compiled again after being forgotten, by
contraction or eviction), against new contexts. From a trace (`just trace`).

    tools/version_repeats.py LINE [--slices 4] [--nearest N] [--trace working/lunacy.fxt]
"""
import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from trace_sql import connect


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('line', type=int)
    ap.add_argument('--slices', type=int, default=4)
    ap.add_argument('--trace', default='working/lunacy.fxt')
    ap.add_argument('--nearest', type=int, default=0, help='diff this many late versions against their closest earlier one')
    args = ap.parse_args()
    rows = list(connect(args.trace).query(
        f"select ts, pc, context from spec_version where line = {args.line} and outcome = 'new' order by ts"))
    if not rows:
        print('(no versions)')
        return
    t0, t1 = rows[0].ts, rows[-1].ts + 1
    seen = set()
    counts = [[0, 0] for _ in range(args.slices)]
    for r in rows:
        s = (r.ts - t0) * args.slices // (t1 - t0)
        key = (r.pc, r.context)
        counts[s][key in seen] += 1
        seen.add(key)
    print('slice  new contexts  repeated contexts')
    for s, (new, repeated) in enumerate(counts):
        print(f'{s:5}  {new:12}  {repeated:17}')
    if args.nearest:
        # How each of the first new contexts of the last slices differs from the closest earlier
        # one at its point and with its greens.
        import difflib, re
        tokens = lambda c: re.split(r'(?<=[,\])}]) ', c)
        greens = lambda c: c[c.find('greens'):]
        earlier_contexts = {}
        for r in rows:
            earlier_contexts.setdefault((r.pc, r.context), r.ts)
        # New contexts only: one an earlier version had is a repeat, counted above.
        late = [r for r in rows if (r.ts - t0) * args.slices // (t1 - t0) >= args.slices // 2
                and earlier_contexts[(r.pc, r.context)] == r.ts]
        for r in late[:args.nearest]:
            earlier = [e for e in rows if e.ts < r.ts and e.pc == r.pc and greens(e.context) == greens(r.context)]
            if not earlier:
                print(f'\n{r.ts / 1e9:.4f}s pc {r.pc}: no earlier version with its greens')
                continue
            best = min(earlier, key=lambda e: sum(d[0] in '+-' for d in difflib.ndiff(tokens(e.context), tokens(r.context))))
            diff = [d for d in difflib.ndiff(tokens(best.context), tokens(r.context)) if d[0] in '+-']
            print(f'\n{r.ts / 1e9:.4f}s pc {r.pc} vs {best.ts / 1e9:.4f}s: ' + ' | '.join(diff))


if __name__ == '__main__':
    main()
