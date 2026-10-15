#!/usr/bin/env python3
"""How often the JIT's compiled code runs: each compiled block's code bytes (from the annotated
disassembly, `jit_disasm`) by how many times its code ran (`block_counts.txt`, feature
`block_counts`), in buckets of executions, and the functions holding the most code that ran
rarely.

    tools/block_counts.py working/jit_disasm.txt working/block_counts.txt
"""
import argparse
import re
import sys
from collections import Counter, defaultdict

sys.path.insert(0, __import__('os').path.dirname(__file__))
from jit_samples import read_disasm

BLOCK = re.compile(r'block (\d+) \(pc (\d+), function ([^,]+),')
BUCKETS = [0, 1, 10, 100, 1000, 10000, 100000]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('disasm')
    ap.add_argument('counts')
    ap.add_argument('--rare', type=int, default=100, help='executions under which code ran rarely')
    ap.add_argument('--by-point', action='store_true', help='compiled blocks per function and PC: the points with the most')
    ap.add_argument('--top', type=int, default=15)
    args = ap.parse_args()

    ranges, insts = read_disasm(args.disasm)
    size, function, pc = Counter(), {}, {}
    for i, (addr, r, _, notes) in enumerate(insts):
        base, length, _ = ranges[r]
        following = insts[i + 1][0] if i + 1 < len(insts) and insts[i + 1][1] == r else base + length
        for note in notes:
            if m := BLOCK.match(note):
                block = int(m.group(1))
                size[block] += following - addr
                pc[block] = int(m.group(2))
                function[block] = m.group(3)
                break
    jit, interpreted = Counter(), Counter()
    for line in open(args.counts):
        if line.startswith('#') or not line.strip():
            continue
        block, j, n = map(int, line.split())
        jit[block], interpreted[block] = j, n

    code = sum(size.values())
    print(f'{len(size)} compiled blocks, {code} bytes; executions in JIT code {sum(jit.values())}, in the interpreter {sum(interpreted.values())}')
    print(f'  {"JIT executions":>18} {"blocks":>7} {"bytes":>9} {"share":>6}')
    for low, high in zip(BUCKETS, BUCKETS[1:] + [None]):
        blocks = [b for b in size if jit[b] >= low and (high is None or jit[b] < high)]
        span = f'{low}+' if high is None else (f'{low}' if high == low + 1 else f'{low}-{high - 1}')
        taken = sum(size[b] for b in blocks)
        print(f'  {span:>18} {len(blocks):7} {taken:9} {100 * taken / code:5.1f}%')

    rare = defaultdict(int)
    for b in size:
        if jit[b] < args.rare:
            rare[function[b]] += size[b]
    print(f'\nfunctions with the most code run under {args.rare} times in JIT code:')
    for f, n in sorted(rare.items(), key=lambda item: -item[1])[:args.top]:
        print(f'  {n:8} bytes  {f}')

    if args.by_point:
        # Compiled blocks at each point: versions of it, and subblocks inside them, compiled.
        points = defaultdict(list)
        for b in size:
            points[(function[b], pc[b])].append(b)
        print(f'\npoints with the most compiled blocks (function, pc: blocks, bytes, JIT executions):')
        for (f, p), blocks in sorted(points.items(), key=lambda item: -len(item[1]))[:args.top]:
            print(f'  {f} pc {p}: {len(blocks)} blocks, {sum(size[b] for b in blocks)} bytes, '
                  f'{sum(jit[b] for b in blocks)} executions')


if __name__ == '__main__':
    main()
