#!/usr/bin/env python3
"""Where a run's JIT code goes, in bytes: from its annotated disassembly
(`just jit-disasm`, working/jit_disasm.txt), the code of each function, each
block, and each kind of residual (a window op by its op), and the code between
residuals (region prologues, window loads, constant pools) by what it does.

    jit_code_size.py [working/jit_disasm.txt] [--top N] [--function LINE] [--vs BASE]

`--function` counts only the code of the function defined at that line.
`--by-pc` also prints, per function and pc, how many blocks the JIT emitted
there and their bytes. `--vs BASE` prints instead how the code differs from
BASE's (another run's annotated disassembly): by function, by kind, and by pc.
"""
import argparse
import re
from collections import Counter

# The instruction classes `jit_samples --classes` splits samples by.
from jit_samples import SLOT, MOVE, TAG

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
    ap.add_argument('--vs', help="another run's disassembly, to print the differences from")
    ap.add_argument('--duplicates', action='store_true', help="blocks compiled into more than one region, and the bytes of their copies past the first")
    ap.add_argument('--where', metavar='KIND', help="each function and pc holding a kind of residual, as `by kind` names it: its uses and bytes there")
    ap.add_argument('--classes', action='store_true', help="bytes by what the instruction is, as jit_samples --classes splits samples: a stack slot's load or store, a move between registers, one with the pinned tag, or anything else; and the kinds of code with the most bytes of moves")
    args = ap.parse_args()
    if args.vs:
        vs(measure(args.vs, args.function), measure(args.disasm, args.function), args.top)
        return
    if args.duplicates:
        duplicates(args.disasm, args.top)
        return
    if args.where:
        where(args.disasm, args.where, args.top)
        return
    by_function, by_block, by_kind, uses, blocks_of, region_total, by_class = measure(args.disasm, args.function)
    report(by_function, by_block, by_kind, uses, blocks_of, region_total, args)
    if args.classes:
        total = sum(by_kind.values())
        print('\nby instruction class:')
        for c in ['slot', 'move', 'tag', 'rest']:
            n = sum(v for (k, what), v in by_class.items() if what == c)
            print(f'  {n:>7} bytes {100 * n / total:5.1f}%  {c}')
        print('\nmoves, by kind:')
        moves = Counter({k: v for (k, what), v in by_class.items() if what == 'move'})
        for k, n in moves.most_common(args.top):
            print(f'  {n:>7} bytes {100 * n / total:5.1f}%  {k}')


def where(path, wanted, top):
    """Each function and pc whose blocks hold residuals of kind `wanted`, by the inline chain of the
    code (`837-1035` is 1035 inlined into 837's code; the pc is the last function's): their uses and
    bytes."""
    uses, sizes = Counter(), Counter()
    at = kind = None
    for line in open(path):
        if REGION.match(line) or OTHER.match(line):
            at = kind = None
        elif m := re.match(r'^\s*; block \d+ \(pc (\d+), function ([^,)]+)', line):
            at, kind = (m.group(2), int(m.group(1))), None
        elif m := RESIDUAL.match(line):
            kind = f'{m.group(1)}({m.group(2)})' if m.group(2) else m.group(1)
            if kind == wanted and at:
                uses[at] += 1
        elif (m := INSN.match(line)) and kind == wanted and at:
            sizes[at] += len(m.group(1)) // 2
    print(f'{sum(uses.values())} uses, {sum(sizes.values())} bytes of {wanted}')
    for (chain, pc), n in uses.most_common(top):
        print(f'  {chain:<24} pc {pc:<4} {n:>4} uses {sizes[(chain, pc)]:>7} bytes')


def duplicates(path, top):
    """Each block's copies, one per region compiling it: the blocks with more than one, and what
    the copies past the first cost."""
    copies, sizes, function_of = Counter(), Counter(), {}
    block = None
    for line in open(path):
        if REGION.match(line) or OTHER.match(line):
            block = None
        elif m := BLOCK.match(line):
            block = int(m.group(1))
            copies[block] += 1
        elif block is not None and (m := INSN.match(line)):
            sizes[block] += len(m.group(1)) // 2
        if m := re.search(r'; block (\d+) \(pc \d+, function (\d+)', line):
            function_of[int(m.group(1))] = m.group(2)
    repeated = {b: n for b, n in copies.items() if n > 1}
    # A block's bytes are summed over its copies, so a copy's are the average.
    extra = sum(sizes[b] * (n - 1) // n for b, n in repeated.items())
    print(f'{sum(copies.values())} blocks compiled, {len(copies)} distinct; {len(repeated)} in more than one region, '
          f'their copies past the first {extra} bytes')
    by_function = Counter()
    for b, n in repeated.items():
        by_function[function_of.get(b, '?')] += sizes[b] * (n - 1) // n
    for function, extra in by_function.most_common(top):
        print(f'  :{function:<6} {extra:>8} bytes of copies')


def measure(path, only):
    """Bytes by function, block, and kind; uses of each kind; each function's blocks; and the
    regions' bytes."""
    by_function, by_block, by_kind, uses, blocks_of, by_class = Counter(), Counter(), Counter(), Counter(), {}, Counter()
    region_total = 0
    function = block = kind = None
    for line in open(path):
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
            if not only or function == only:
                uses[kind] += 1
            continue
        if m := COMMENT.match(line):
            # Code the JIT lays out around residuals, by what it does, but for
            # the indented notes inside a residual's own code.
            if not line.startswith('  ;         '):
                kind = re.sub(r'\d+', 'N', m.group(1).split(',')[0].split('{')[0]).strip()
            continue
        if m := INSN.match(line):
            if only and function != only:
                continue
            size = len(m.group(1)) // 2
            by_function[function] += size
            by_kind[kind] += size
            text = line[m.end():]
            by_class[(kind, 'slot' if SLOT.search(text) else 'move' if MOVE.search(text) else 'tag' if TAG.search(text) else 'rest')] += size
            if block:
                by_block[block] += size
                blocks_of.setdefault(function, set()).add(block[1])
    return by_function, by_block, by_kind, uses, blocks_of, region_total, by_class


def per_pc(by_block):
    pcs = {}
    for (f, _, pc), n in by_block.items():
        blocks, size = pcs.get((f, pc), (0, 0))
        pcs[(f, pc)] = (blocks + 1, size + n)
    return pcs


def vs(base, this, top):
    (bf, bb, bk, bu, bbl, _, _), (tf, tb, tk, tu, tbl, _, _) = base, this
    print(f'{sum(bk.values())} -> {sum(tk.values())} bytes of code, '
          f'{sum(len(b) for b in bbl.values())} -> {sum(len(b) for b in tbl.values())} blocks')
    print('\nby function (line):')
    for f in sorted(set(bf) | set(tf), key=lambda f: -abs(tf[f] - bf[f])):
        print(f'  {":" + f if f.isdigit() else f:<7} {bf[f]:>7} -> {tf[f]:<7} {tf[f] - bf[f]:+7}  '
              f'{len(bbl.get(f, ()))} -> {len(tbl.get(f, ()))} blocks')
    print('\nby kind (bytes, uses, bytes each):')
    each = lambda n, u: f'{n / u:.0f}' if u else '-'
    for k in sorted(set(bk) | set(tk), key=lambda k: -abs(tk[k] - bk[k]))[:top]:
        print(f'  {tk[k] - bk[k]:+7}  {bk[k]:>6} -> {tk[k]:<6} {bu[k]:>4} -> {tu[k]:<4} {each(bk[k], bu[k]):>4} -> {each(tk[k], tu[k]):<4} {k}')
    print('\nby pc (function, pc: blocks, bytes):')
    bp, tp = per_pc(bb), per_pc(tb)
    for key in sorted(set(bp) | set(tp), key=lambda key: -abs(tp.get(key, (0, 0))[1] - bp.get(key, (0, 0))[1]))[:top]:
        (b0, n0), (b1, n1) = bp.get(key, (0, 0)), tp.get(key, (0, 0))
        print(f'  :{key[0]} pc {key[1]:>4}: {b0:>3} -> {b1:<3} blocks {n0:>6} -> {n1:<6} {n1 - n0:+6}')


def report(by_function, by_block, by_kind, uses, blocks_of, region_total, args):
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
        for (f, pc), (blocks, size) in sorted(per_pc(by_block).items(), key=lambda item: (item[0][0], int(item[0][1]))):
            print(f'  :{f} pc {pc:>4}: {blocks:>3} blocks {size:>6} bytes')
    print(f'\nlargest blocks (function, block, pc):')
    for b, n in by_block.most_common(args.top):
        print(f'  {n:>7} bytes  :{b[0]} block {b[1]} pc {b[2]}')


if __name__ == '__main__':
    main()
