#!/usr/bin/env python3
"""Count the loads, stores and moves in `window_dump.txt` files.

A dump (`just window-dump`) lists each compiled block with its hotness when
compiled, then the code the window allocator emitted per residual. This totals
that code over every block and over the hot blocks (hotness 0: those entered as
often as the block that triggered compilation), so two allocators' dumps of the
same benchmark can be compared. See docs/bottom-up-allocation.md.
"""
import argparse
import re
import sys

BLOCK = re.compile(r'^block (\d+) hotness (\d+) entered with ')
STUB = re.compile(r'^block \d+ compiled already, entered with \{[^}]*\}: (.*)$')
EMIT = re.compile(r'(\w+|\[\d+\]) <- (\w+|\[\d+\])')


def emits(text):
    """(loads, stores, moves) in one line of allocator code."""
    counts = [0, 0, 0]
    for dst, src in EMIT.findall(text):
        if src.startswith('['):
            counts[0] += 1
        elif dst.startswith('['):
            counts[1] += 1
        else:
            counts[2] += 1
    return counts


def tally(path):
    """{'all': [l, s, m], 'hot': [l, s, m]} over the dump at `path`."""
    totals = {'all': [0, 0, 0], 'hot': [0, 0, 0]}
    hot = False
    for line in open(path):
        line = line.rstrip('\n')
        m = BLOCK.match(line)
        if m:
            hot = m.group(2) == '0'
            continue
        m = STUB.match(line)
        if m:
            code = m.group(1)
        elif line.startswith('      ') and not line.lstrip().startswith(('window ', 'tests ')):
            code = line
        else:
            continue
        counts = emits(code)
        for key in ('all', 'hot') if hot else ('all',):
            totals[key] = [a + b for a, b in zip(totals[key], counts)]
    return totals


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('dumps', nargs='+', help='window_dump.txt files')
    args = parser.parse_args()
    print('%-50s %22s %22s' % ('dump', 'all: loads stores moves', 'hot: loads stores moves'))
    for path in args.dumps:
        t = tally(path)
        print('%-50s %22s %22s' % (path, '%d %d %d' % tuple(t['all']), '%d %d %d' % tuple(t['hot'])))
    return 0


if __name__ == '__main__':
    sys.exit(main())
