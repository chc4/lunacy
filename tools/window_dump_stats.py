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
jumps into compiled blocks, other jumps, exits, ops) in each dump. With `--ops`,
it lists how often each window op ran (a residual `window(Op, ...)` or
`guard_dynamic(Op, ...)`, counted by its `op at` line) in each dump side by
side, most changed first. With `--ngrams N`, it lists the most executed runs of
N residuals adjacent in a block, over all the dumps: a residual ran as often as
its counted code, or as the residual before it with none (a guard, a select;
a thunk, a side exit, runs nothing),
and a run as often as its last residual.
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
RESIDUAL = re.compile(r'^    \d+ (window|guard_dynamic)\((\w+)')
# Any residual: its kind, and a window op's, a guard's or an exec's name.
ANY_RESIDUAL = re.compile(r'^    \d+ ([a-z_]+)(?:\(([A-Za-z_]+|\d+, (\w+)))?')


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


def residuals(path):
    """[(block, residual name, times run)] over the dump at `path`, in order."""
    runs, found = {}, []
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
            continue
        m = ANY_RESIDUAL.match(line)
        if m:
            kind, arg, guarded = m.groups()
            # A guard's expected type, not a native guard's pointer.
            if guarded is not None and guarded.startswith('0x'):
                guarded = None
            name = kind if arg is None else '%s(%s)' % (kind, guarded or ('' if arg.isdigit() else arg))
            found.append([block, name, None])
            continue
        m = COUNTED.search(line)
        if m and found and found[-1][2] is None and line.startswith('      '):
            found[-1][2] = int(m.group(1))
    # A residual with no counted code of its own ran as often as the one before it.
    # A thunk is a side exit, compiling on its first run, so it runs nothing.
    result, last = [], (None, 0)
    for block, name, id in found:
        if name == 'thunk':
            continue
        n = runs.get(id, 0) if id is not None else (last[1] if last[0] == block else 0)
        result.append((block, name, n))
        last = (block, n)
    return result


def ngrams(paths, n):
    """{run of `n` residual names: times run} over the dumps at `paths`."""
    totals = {}
    for path in paths:
        found = residuals(path)
        for i in range(len(found) - n + 1):
            window = found[i:i + n]
            if len({block for block, _, _ in window}) != 1:
                continue
            key = tuple(name for _, name, _ in window)
            totals[key] = totals.get(key, 0) + window[-1][2]
    return totals


def ops(path):
    """{window op: times run} over the dump at `path`."""
    runs, seen = {}, []
    op = None
    for line in open(path):
        line = line.rstrip('\n')
        m = COUNT.match(line)
        if m:
            runs[int(m.group(1))] = int(m.group(2))
            continue
        m = RESIDUAL.match(line)
        if m:
            op = m.group(2)
            continue
        if line.startswith('    ') and not line.startswith('      '):
            op = None
        m = COUNTED.search(line)
        if m and op is not None and 'op at' in line:
            seen.append((op, int(m.group(1))))
            op = None
    totals = {}
    for op, id in seen:
        totals[op] = totals.get(op, 0) + runs.get(id, 0)
    return totals


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
    parser.add_argument('--ops', action='store_true', help='how often each window op ran, in each dump')
    parser.add_argument('--ngrams', type=int, metavar='N', help='the most executed runs of N adjacent residuals, over all dumps')
    args = parser.parse_args()
    global RAW
    RAW = args.raw
    if args.ngrams:
        totals = ngrams(args.dumps, args.ngrams)
        executed = sum(n for path in args.dumps for _, _, n in residuals(path))
        print('residuals run: %d' % executed)
        for key, n in sorted(totals.items(), key=lambda kv: -kv[1])[:args.top or 40]:
            print('%14d %5.1f%%  %s' % (n, 100 * n / executed, ' ; '.join(key)))
        return 0
    if args.ops:
        per = [ops(path) for path in args.dumps]
        names = sorted({op for t in per for op in t}, key=lambda op: -(max(t.get(op, 0) for t in per) - min(t.get(op, 0) for t in per)))
        print('%-24s' % 'op' + ''.join('%20s' % path.split('/')[-2 if path.endswith('window_dump.txt') and '/' in path else -1] for path in args.dumps))
        for op in names:
            print('%-24s' % op + ''.join('%20d' % t.get(op, 0) for t in per))
        print('%-24s' % 'total' + ''.join('%20d' % sum(t.values()) for t in per))
        return 0
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
