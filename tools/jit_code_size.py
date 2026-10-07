#!/usr/bin/env python3
"""Where a run's JIT code goes, in bytes: from its annotated disassembly
(`just jit-disasm`, working/jit_disasm.txt), the code of each function, each
block, and each kind of residual (a window op by its op), and the code between
residuals (region prologues, window loads, constant pools) by what it does.

    jit_code_size.py [working/jit_disasm.txt] [--top N] [--function LINE]

`--function` counts only the code of the function defined at that line.
`--by-pc` also prints, per function and pc, how many blocks the JIT emitted
there and their bytes.
"""
import argparse
import re
from collections import Counter

REGION = re.compile(r'^==== region entered at block \d+, function :(\d+) @ \S+, (\d+) bytes')
# Other committed code (thunk stubs, the shared snapshot code), by its title.
OTHER = re.compile(r'^==== (.*?)(?: into block \d+)? @ ')
BLOCK = re.compile(r'^\s*; block (\d+) \(pc (\d+)')
RESIDUAL = re.compile(r'^\s*;\s+\d+ (\w+)(?:\((\w+))?')
COMMENT = re.compile(r'^\s*;\s*(.*)')
INSN = re.compile(r'^\s*[0-9a-f]+ \+[0-9a-f]+\s+([0-9a-f]+)\s')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('disasm', nargs='?', default='working/jit_disasm.txt')
    ap.add_argument('--top', type=int, default=20)
    ap.add_argument('--function', help="only the function defined at this line")
    ap.add_argument('--by-pc', action='store_true', help='blocks and bytes per function and pc')
    args = ap.parse_args()

    by_function, by_block, by_kind, uses, blocks_of = Counter(), Counter(), Counter(), Counter(), {}
    region_total = 0
    function = block = kind = None
    for line in open(args.disasm):
        if m := REGION.match(line):
            function, block, kind = m.group(1), None, 'region prologue'
            region_total += int(m.group(2))
            continue
        if m := OTHER.match(line):
            function, block, kind = m.group(1), None, m.group(1)
            continue
        if m := BLOCK.match(line):
            block, kind = (function, int(m.group(1)), int(m.group(2))), 'block entry'
            continue
        if m := RESIDUAL.match(line):
            kind = f'{m.group(1)}({m.group(2)})' if m.group(2) else m.group(1)
            if not args.function or function == args.function:
                uses[kind] += 1
            continue
        if m := COMMENT.match(line):
            # Code the JIT lays out around residuals, by what it does, but for
            # the indented notes inside a residual's own code.
            if not line.startswith('  ;         '):
                kind = re.sub(r'\d+', 'N', m.group(1).split(',')[0].split('{')[0]).strip()
            continue
        if m := INSN.match(line):
            if args.function and function != args.function:
                continue
            size = len(m.group(1)) // 2
            by_function[function] += size
            by_kind[kind] += size
            if block:
                by_block[block] += size
                blocks_of.setdefault(function, set()).add(block[1])

    total = sum(by_kind.values())
    print(f'{total} bytes of code ({region_total} in the regions, with their constant pools), {sum(len(b) for b in blocks_of.values())} blocks')
    print('\nby function (line):')
    for f, n in by_function.most_common():
        print(f'  {":" + f if f.isdigit() else f:<7} {n:>7} bytes {100 * n / total:5.1f}%  {len(blocks_of.get(f, ()))} blocks')
    print('\nby kind:')
    for k, n in by_kind.most_common(args.top):
        each = f'  {uses[k]} uses, {n / uses[k]:.0f} bytes each' if uses[k] else ''
        print(f'  {n:>7} bytes {100 * n / total:5.1f}%  {k}{each}')
    if args.by_pc:
        print('\nby pc (function, pc: blocks, bytes):')
        per_pc = {}
        for (f, _, pc), n in by_block.items():
            blocks, size = per_pc.get((f, pc), (0, 0))
            per_pc[(f, pc)] = (blocks + 1, size + n)
        for (f, pc), (blocks, size) in sorted(per_pc.items(), key=lambda item: (item[0][0], int(item[0][1]))):
            print(f'  :{f} pc {pc:>4}: {blocks:>3} blocks {size:>6} bytes')
    print(f'\nlargest blocks (function, block, pc):')
    for b, n in by_block.most_common(args.top):
        print(f'  {n:>7} bytes  :{b[0]} block {b[1]} pc {b[2]}')


if __name__ == '__main__':
    main()
