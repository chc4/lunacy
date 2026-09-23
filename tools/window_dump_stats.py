#!/usr/bin/env python3
"""Count the loads, stores and moves in `window_dump.txt` files.

A dump (`just window-dump`) lists each compiled block with its hotness when
compiled, then the code the window allocator emitted per residual. This totals
that code over every block and over the hot blocks (hotness 0: those entered as
often as the block that triggered compilation), so two allocators' dumps of the
same benchmark can be compared. With `--blocks`, it lists each hot block's
counts in every dump side by side instead (every block's, with `--all`), where
they differ. See docs/bottom-up-allocation.md.
"""
import argparse
import re
import sys

BLOCK = re.compile(r'^block (\d+) hotness (\d+) entered with ')
STUB = re.compile(r'^(?:block \d+ compiled already, entered with \{[^}]*\}|region entry block \d+ loads)[:]? ?(.*)$')
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


def blocks(path):
    """{block id: (hot, [loads, stores, moves])} over the dump at `path`, entry
    stubs counted with the block they enter."""
    found = {}
    current = None
    for line in open(path):
        line = line.rstrip('\n')
        m = BLOCK.match(line)
        if m:
            current = int(m.group(1))
            found.setdefault(current, [m.group(2) == '0', [0, 0, 0]])
            continue
        m = STUB.match(line)
        if m:
            code = m.group(1)
        elif current is not None and line.startswith('      ') and not line.lstrip().startswith(('window ', 'tests ')):
            code = line
        else:
            continue
        if current is None:
            continue
        found[current][1] = [a + b for a, b in zip(found[current][1], emits(code))]
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('dumps', nargs='+', help='window_dump.txt files')
    parser.add_argument('--blocks', action='store_true', help="each hot block's counts, side by side")
    parser.add_argument('--all', action='store_true', help='with --blocks, every block, not just the hot ones')
    args = parser.parse_args()
    found = [blocks(path) for path in args.dumps]
    if args.blocks:
        ids = sorted({b for dump in found for b, (hot, _) in dump.items() if hot or args.all})
        print('%-8s' % 'block' + ''.join('%24s' % path.split('/')[-1] for path in args.dumps))
        for b in ids:
            cells = ['%d %d %d' % tuple(dump[b][1]) if b in dump else '-' for dump in found]
            if len(set(cells)) > 1:
                print('%-8d' % b + ''.join('%24s' % cell for cell in cells))
        return 0
    print('%-50s %22s %22s' % ('dump', 'all: loads stores moves', 'hot: loads stores moves'))
    for path, dump in zip(args.dumps, found):
        total = [0, 0, 0]
        hot = [0, 0, 0]
        for is_hot, counts in dump.values():
            total = [a + b for a, b in zip(total, counts)]
            if is_hot:
                hot = [a + b for a, b in zip(hot, counts)]
        print('%-50s %22s %22s' % (path, '%d %d %d' % tuple(total), '%d %d %d' % tuple(hot)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
