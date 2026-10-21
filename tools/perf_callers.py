#!/usr/bin/env python3
"""Who calls a function, by samples: from `perf script` output of a profile
recorded with call graphs (`perf record --call-graph fp`), the samples whose
leaf frame matches `symbol`, counted by their caller's frame (JIT blocks by the
Lua line their perf map names them with, as in tools/perf_jit_lines.py), side
by side for each profile, with the difference between the first two. With
`--callees`, it counts the samples with `symbol` anywhere on their stack, by
what the outermost match called, to show where a function's inclusive time
goes. Inlined functions count as calls, and `(self)` is time in the function.

    perf script -i A.data > a.txt; perf script -i B.data > b.txt
    tools/perf_callers.py SYMBOL a.txt b.txt [--top N] [--inner | --callees]
"""
import argparse
import re
import sys
from collections import Counter

FRAME = re.compile(r'^\s+[0-9a-f]+\s+(.*?)\s+\((.*)\)$')
JIT = re.compile(r'^jit_block_\d+ :(\d+)')


def name(sym):
    jit = JIT.match(sym)
    return f'JIT line {jit.group(1)}' if jit else re.sub(r'\+0x[0-9a-f]+$', '', sym)


def callee(frames, symbol):
    """What the outermost frame matching `symbol` called, on a sample's stack
    (`frames`, leaf first). `(self)` if the match is the leaf, None if none."""
    flat = [sym for frame in frames for sym in frame]
    for k in range(len(flat) - 1, -1, -1):
        if symbol in flat[k]:
            return name(flat[k - 1]) if k > 0 else '(self)'
    return None


def callers(path, symbol, inner, below=False):
    """Per caller, the samples whose leaf frame has `symbol` in it. A frame is a
    machine frame: the functions inlined into it (`(inlined)` lines) and it.
    With `inner`, counted by the leaf frame's innermost function instead. With
    `below`, counted by what `symbol` called, anywhere on the stack."""
    counts = Counter()
    frames, inlined = [], []
    for line in list(open(path, errors='replace')) + ['']:
        m = FRAME.match(line)
        if m:
            inlined.append(m.group(1))
            if m.group(2) != 'inlined':
                frames.append(inlined)
                inlined = []
            continue
        if frames and below:
            called = callee(frames, symbol)
            if called is not None:
                counts[called] += 1
            frames, inlined = [], []
        elif frames:
            if any(symbol in sym for sym in frames[0]):
                if inner:
                    counts[name(frames[0][0])] += 1
                else:
                    counts[name(frames[1][-1]) if len(frames) > 1 else '(no caller)'] += 1
            frames, inlined = [], []
    return counts


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('symbol')
    ap.add_argument('scripts', nargs='+')
    ap.add_argument('--top', type=int, default=20)
    ap.add_argument('--inner', action='store_true', help="count by the leaf frame's innermost function, not the caller")
    ap.add_argument('--callees', action='store_true', help='count the samples with symbol on their stack by what it called')
    args = ap.parse_args()
    counts = [callers(p, args.symbol, args.inner, args.callees) for p in args.scripts]
    keys = sorted(set().union(*counts), key=lambda k: -max(c[k] for c in counts))[:args.top]
    width = min(90, max((len(k) for k in keys), default=10))
    print(f'{"callee" if args.callees else "caller":{width}}' + ''.join(f'{p.split("/")[-1][:14]:>16}' for p in args.scripts) + ('    delta' if len(counts) > 1 else ''))
    for k in keys:
        tail = f'{counts[-1][k] - counts[0][k]:+9}' if len(counts) > 1 else ''
        print(f'{k[:width]:{width}}' + ''.join(f'{c[k]:>16}' for c in counts) + tail)
    print(f'{"all":{width}}' + ''.join(f'{sum(c.values()):>16}' for c in counts))


if __name__ == '__main__':
    sys.exit(main())
