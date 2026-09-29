#!/usr/bin/env python3
"""The allocator code a run executed most, from its `window_dump.txt` (`just
window-dump`): how many loads, stores and moves ran in all, and the counted
pieces of allocator code that moved values, hottest first, each with its block,
the block's pc and entry window, and the residual (or jump, exit, entry) it
belongs to. With `--blocks`, the loads, stores and moves each block ran
instead (its own code and its jumps out), hottest first.

    window_hot.py [working/window_dump.txt] [--top N] [--blocks]
"""
import argparse
import re
from collections import Counter

BLOCK = re.compile(r'^block (\d+) hotness (\d+)(?: pc (\d+))? entered with (\{[^}]*\})')
RESIDUAL = re.compile(r'^  [ \d]{2}\d (.*)$')
COUNTED = re.compile(r'^\s*(.*?) #(\d+)$')
COUNT = re.compile(r'^count #(\d+) (\d+)$')
EMIT = re.compile(r'(\w+|\[\d+\]) <- (\w+|\[\d+\])')


def kind(dst, src):
    if dst.startswith('['):
        return 'store'
    return 'load' if src.startswith('[') else 'move'


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('dump', nargs='?', default='working/window_dump.txt')
    ap.add_argument('--top', type=int, default=30)
    ap.add_argument('--blocks', action='store_true', help="each block's executed loads, stores and moves instead")
    args = ap.parse_args()

    pieces, counts = {}, {}
    block = residual = None
    for line in open(args.dump):
        line = line.rstrip('\n')
        if m := COUNT.match(line):
            counts[int(m.group(1))] = int(m.group(2))
            continue
        if m := BLOCK.match(line):
            block, residual = (m.group(1), m.group(3), m.group(4)), None
            continue
        if m := RESIDUAL.match(line):
            residual = m.group(1)
            continue
        if m := COUNTED.match(line):
            text, id = m.group(1), int(m.group(2))
            emits = EMIT.findall(text)
            if emits:
                # A line outside a block (a region entry, a linked thunk) is its
                # own place.
                where = block if not line.startswith(' ') or block is None else block
                pieces[id] = (where if line.startswith(' ') else None, residual if line.startswith(' ') else None, text, emits)

    totals = Counter()
    for id, (_, _, _, emits) in pieces.items():
        for dst, src in emits:
            totals[kind(dst, src)] += counts.get(id, 0)
    print(f"executed: {totals['load']} loads, {totals['store']} stores, {totals['move']} moves")
    print()
    if args.blocks:
        by_block = {}
        for id, (block, _, _, emits) in pieces.items():
            if block is None:
                continue
            ran = by_block.setdefault(block, Counter())
            for dst, src in emits:
                ran[kind(dst, src)] += counts.get(id, 0)
        print(f"{'loads':>10} {'stores':>10} {'moves':>10}  block")
        for block, ran in sorted(by_block.items(), key=lambda b: -sum(b[1].values()))[:args.top]:
            print(f"{ran['load']:>10} {ran['store']:>10} {ran['move']:>10}  block {block[0]} pc {block[1]} {block[2]}")
        return
    hottest = sorted(pieces, key=lambda id: -counts.get(id, 0))[:args.top]
    for id in hottest:
        block, residual, text, _ = pieces[id]
        where = f'block {block[0]} pc {block[1]} {block[2]}' if block else 'outside a block'
        print(f'{counts.get(id, 0):>10}  {where}')
        if residual:
            print(f'{"":>10}    at {residual[:110]}')
        print(f'{"":>10}    {text[:160]}')


if __name__ == '__main__':
    main()
