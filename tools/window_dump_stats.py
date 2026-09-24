#!/usr/bin/env python3
"""Count the loads, stores and moves in `window_dump.txt` files.

A dump (`just window-dump`) lists each compiled block with its hotness when
compiled, then the code the window allocator emitted per residual. This totals
that code over every block and over the hot blocks (hotness 0: those entered as
often as the block that triggered compilation), so two allocators' dumps of the
same benchmark can be compared. Each line of emitted code ends with ` #id`
and the dump with how often each ran (`count #id n`), so it also totals the
code weighted by how often it ran, by log2(1 + log2(1 + n)): zero for code
that never ran, and growing slowly enough that the hottest edge doesn't
swamp the rest. With `--blocks`, it lists each hot block's counts in
every dump side by side instead (every block's, with `--all`), where they
differ. With `--kinds`, it totals the code by what emitted it (region entries,
jumps into compiled blocks, other jumps, exits, ops) in each dump.
"""
import argparse
import math
import re
import sys

BLOCK = re.compile(r'^block (\d+) hotness (\d+)(?: pc \d+)? entered with ')
STUB = re.compile(r'^(?:block \d+ compiled already, entered with \{[^}]*\}|region entry block \d+ loads)[:]? ?(.*)$')
EMIT = re.compile(r'(\w+|\[\d+\]) <- (\w+|\[\d+\])')
COUNTED = re.compile(r' #(\d+)$')
COUNT = re.compile(r'^count #(\d+) (\d+)$')


RAW = False


def weight(runs):
    """How much code that ran `runs` times counts: `runs` itself with `--raw`."""
    return runs if RAW else math.log2(1 + math.log2(1 + runs))


def counted(path):
    """(block, code line, runs, [loads, stores, moves] weighted by `weight`) per
    counted line."""
    lines, runs = [], {}
    block = None
    for line in open(path):
        line = line.rstrip('\n')
        m = COUNT.match(line)
        if m:
            runs[int(m.group(1))] = int(m.group(2))
            continue
        m = BLOCK.match(line)
        if m:
            block = int(m.group(1))
        m = COUNTED.search(line)
        if m:
            lines.append((block, int(m.group(1)), line[:m.start()]))
    return [(block, code, runs.get(id, 0), [n * weight(runs.get(id, 0)) for n in emits(code)]) for block, id, code in lines]


def kind(code):
    """What emitted a counted line of allocator code."""
    code = code.strip()
    if code.startswith('region entry'):
        return 'region entry'
    if 'compiled' in code:
        return 'into compiled'
    if code.startswith('to block'):
        return 'jump'
    if code.startswith('exit'):
        return 'exit'
    return 'op'


KINDS = ['region entry', 'into compiled', 'jump', 'exit', 'op']


def executed(path):
    """[loads, stores, moves] weighted by how often each counted line ran."""
    total = [0, 0, 0]
    for _, _, _, counts in counted(path):
        total = [a + b for a, b in zip(total, counts)]
    return total


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
    parser.add_argument('--blocks', action='store_true', help="each hot block's counts, side by side; with --raw, each block's executed counts")
    parser.add_argument('--all', action='store_true', help='with --blocks, every block, not just the hot ones')
    parser.add_argument('--top', type=int, help='the counted lines executing the most loads, stores and moves')
    parser.add_argument('--raw', action='store_true', help='weight code by how often it ran, not log log of it')
    parser.add_argument('--kinds', action='store_true', help='the code totalled by what emitted it, in each dump')
    args = parser.parse_args()
    global RAW
    RAW = args.raw
    if args.kinds:
        print('%-16s' % 'kind' + ''.join('%34s' % path for path in args.dumps))
        per = []
        for path in args.dumps:
            totals = {k: [0, 0, 0] for k in KINDS}
            for _, code, _, counts in counted(path):
                totals[kind(code)] = [a + b for a, b in zip(totals[kind(code)], counts)]
            per.append(totals)
        for k in KINDS:
            print('%-16s' % k + ''.join('%34s' % ('%.0f %.0f %.0f' % tuple(t[k])) for t in per))
        return 0
    if args.top:
        for path in args.dumps:
            print('==', path)
            lines = sorted(counted(path), key=lambda line: -sum(line[3]))
            for block, code, runs, counts in lines[:args.top]:
                print('%7.1f %7.1f %7.1f  block %s x%d: %s' % (*counts, block, runs, code.strip()))
        return 0
    found = [blocks(path) for path in args.dumps]
    if args.blocks and RAW:
        # Executed counts per block, every block that ran, most first.
        ran = []
        for path in args.dumps:
            per = {}
            for block, _, _, counts in counted(path):
                per[block] = [a + b for a, b in zip(per.get(block, [0, 0, 0]), counts)]
            ran.append(per)
        ids = sorted({b for per in ran for b, counts in per.items() if sum(counts)}, key=lambda b: -max(sum(per.get(b, [0, 0, 0])) for per in ran))
        print('%-8s' % 'block' + ''.join('%28s' % path.split('/')[-1] for path in args.dumps))
        for b in ids:
            print('%-8s' % ('entry' if b is None else b) + ''.join('%28s' % ('%.0f %.0f %.0f' % tuple(per[b]) if b in per else '-') for per in ran))
        return 0
    if args.blocks:
        ids = sorted({b for dump in found for b, (hot, _) in dump.items() if hot or args.all})
        print('%-8s' % 'block' + ''.join('%24s' % path.split('/')[-1] for path in args.dumps))
        for b in ids:
            cells = ['%d %d %d' % tuple(dump[b][1]) if b in dump else '-' for dump in found]
            if len(set(cells)) > 1:
                print('%-8d' % b + ''.join('%24s' % cell for cell in cells))
        return 0
    print('%-44s %22s %22s %26s' % ('dump', 'all: loads stores moves', 'hot: loads stores moves', 'run: loads stores moves'))
    for path, dump in zip(args.dumps, found):
        total = [0, 0, 0]
        hot = [0, 0, 0]
        for is_hot, counts in dump.values():
            total = [a + b for a, b in zip(total, counts)]
            if is_hot:
                hot = [a + b for a, b in zip(hot, counts)]
        print('%-44s %22s %22s %26s' % (path, '%d %d %d' % tuple(total), '%d %d %d' % tuple(hot), '%.0f %.0f %.0f' % tuple(executed(path))))
    return 0


if __name__ == '__main__':
    sys.exit(main())
