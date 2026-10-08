#!/usr/bin/env python3
"""Compare two `just jit-disasm` dumps (working/jit_disasm.txt) of one benchmark
block by block: for each block both have, whether its code is the same once
addresses are dropped (where code and its pool landed, RIP displacements,
in-region jump distances, pool contents), and where it starts relative to a
64-byte line and its size in each.

Prints the blocks whose code differs, with a diff of their instructions, then,
with `--blocks`, the placement of those blocks in each dump (to compare the
placement of hot blocks, as `just jit-profile` lists them).

    tools/jit_disasm_diff.py a/jit_disasm.txt b/jit_disasm.txt [--blocks 204,201]
"""
import argparse
import difflib
import re

INSN = re.compile(r'^  ([0-9a-f]+) \+[0-9a-f]+\s+[0-9a-f]+\s+(.*)$')
BLOCK = re.compile(r'^  ; block (\d+) \(pc (\d+)')


def normalize(text):
    """An instruction's text without what depends on where code landed."""
    target = re.search(r'-> (block \d+)', text)
    text = text.split(';')[0].rstrip()
    text = re.sub(r'\$[+-]0x[0-9a-f]+', '$', text)
    text = re.sub(r'rip [+-] 0x[0-9a-f]+', 'rip', text)
    text = re.sub(r'0x[0-9a-f]{9,}', 'ADDR', text)
    return text + (f'  -> {target.group(1)}' if target else '')


def blocks(path):
    """{block id: (start address, size in bytes, [normalized instructions])}."""
    out, cur = {}, None
    for line in open(path):
        line = line.rstrip('\n')
        if line.startswith('===='):
            cur = None
            continue
        m = BLOCK.match(line)
        if m:
            cur = out.setdefault(int(m.group(1)), [None, 0, []])
            continue
        m = INSN.match(line)
        if m and cur is not None:
            addr, size = int(m.group(1), 16), len(line.split()[2]) // 2
            if cur[0] is None:
                cur[0] = addr
            cur[1] += size
            cur[2].append(normalize(m.group(2)))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('a')
    ap.add_argument('b')
    ap.add_argument('--blocks', default='', help='comma-separated block ids to show placement of')
    args = ap.parse_args()
    a, b = blocks(args.a), blocks(args.b)
    only = sorted(set(a) ^ set(b))
    if only:
        print(f'blocks in only one dump: {only}')
    differ = [id for id in sorted(set(a) & set(b)) if a[id][2] != b[id][2]]
    print(f'{len(set(a) & set(b))} blocks in both, {len(differ)} with different code')
    for id in differ:
        print(f'\n== block {id}: {a[id][1]} / {b[id][1]} bytes')
        for line in difflib.unified_diff(a[id][2], b[id][2], lineterm='', n=1):
            if not line.startswith(('---', '+++')):
                print(line)
    if args.blocks:
        print('\nblock   a: start%64 bytes   b: start%64 bytes')
        for id in (int(i) for i in args.blocks.split(',')):
            fmt = lambda d: f'{d[id][0] % 64:>8} {d[id][1]:>5}' if id in d else f'{"-":>14}'
            print(f'{id:>5}  {fmt(a)}     {fmt(b)}')


if __name__ == '__main__':
    main()
