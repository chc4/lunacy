#!/usr/bin/env python3
"""A profile's samples on the JIT's code, joined to its disassembly.

    tools/jit_samples.py JIT_DISASM SAMPLES [--out FILE] [--hot-blocks FILE] [--op NOTE] [--top N]

JIT_DISASM is the `jit_disasm.txt` a run writes (feature `jit_disasm`), and
SAMPLES that same run's samples, `perf script -F ip,sym` (a sample's address,
then its symbol), so the addresses agree: `just jit-profile` makes both. With
precise samples (IBS), a sample's address is the instruction that ran.

Prints the samples' split between the JIT's code and the binary's functions,
the JIT's by what emitted the code (the disassembly's notes: a region's entry
and exit, and a block's residuals and the parts of one) summed over every
copy, and the JIT's by block. `--out` writes the disassembly of every range with a sample, each
instruction with its count; `--hot-blocks` only the blocks with one, whole, in the order they are
laid out: a loop's body, the way its code falls through. `--op` sums the copies of what one note names
(`PushFrame`, `window(GetTableInteger`) instruction by instruction, over the
copies of the same code, and prints each code with its first copy's text.
`--blocks-of` splits the samples of what one note names by block. `--classes` splits the JIT's
samples by kind of code (window ops, guards, control flow, calls and frames, region entry and
exit) and, within each, by what the instruction is: a stack slot's load or store, the window's
traffic with the frame; a move between registers, its shuffles into and out of a stencil's
registers; one with the pinned tag, boxing or unboxing; or the rest. And the window ops' by op.
"""
import argparse
import re
import sys
from bisect import bisect_right
from collections import Counter, defaultdict

RANGE = re.compile(r'^==== (.*) @ 0x([0-9a-f]+), (\d+) bytes$')
NOTE = re.compile(r'^  ; ( *)(.*)$')
INST = re.compile(r'^  ([0-9a-f]+) \+([0-9a-f]+)\s+(.*)$')
INDEX = re.compile(r'^\d+ ')
# A stack slot's load or store: the window's traffic with the frame, at the base pointer.
SLOT = re.compile(r'\[r13( [+-] [^\]]+)?\]')
# A move from one register to another.
MOVE = re.compile(r'\s(?:mov|movq|movaps|vmovaps|vmovq|vmovsd)\s+(?:[re]?[a-z][a-z0-9]*|xmm\d+), (?:[re]?[a-z][a-z0-9]*|xmm\d+)\s*$')
# An instruction with the pinned tag register: boxing or unboxing a value.
TAG = re.compile(r'\br14\b')
# The group of code each kind of note is, but for window ops' own.
GROUPS = {
    **dict.fromkeys(['guard', 'guard_dynamic', 'guard_witness', 'lua_guard', 'native_guard', 'epoch', 'tripped'], 'guard'),
    **dict.fromkeys(['select', 'branch', 'jump', 'thunk', 'from', "an exit's way", 'into a cold stencil'], 'control'),
    **dict.fromkeys(['lcall', 'ncall', 'call', 'ret', 'inline', 'inline_ret', 'enter', 'leave', 'exec',
                     'arrive', 'arrived', 'returned', 'gc'], 'call/frame'),
    **dict.fromkeys(['region entry: prologue', 'exit_jit: epilogue', 'load the entry window',
                     'fill the upvalue cells the entry\'s facts are about', 'constant pool', 'block entry'], 'region'),
}


def kind(note):
    """What a note names, without what's particular to one copy: a residual's
    index and operands, a block's number."""
    note = INDEX.sub('', note)
    if note.startswith('block '):
        return 'block entry'
    if note.startswith(('window(', 'emit(')):
        return note.split(',')[0].rstrip(')') + ')'
    return re.split(r'[( ]', note, 1)[0] if '(' in note else note


def read_disasm(path):
    """Every instruction: (address, range index, line, notes it is under)."""
    ranges, insts = [], []
    notes = []
    for line in open(path):
        line = line.rstrip('\n')
        if m := RANGE.match(line):
            ranges.append((int(m.group(2), 16), int(m.group(3)), m.group(1)))
            notes = []
            continue
        if m := NOTE.match(line):
            depth = len(m.group(1))
            notes = [n for n in notes if n[0] < depth] + [(depth, m.group(2))]
            continue
        if m := INST.match(line):
            insts.append((int(m.group(1), 16), len(ranges) - 1, line, tuple(n for _, n in notes)))
    return ranges, insts


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('disasm')
    ap.add_argument('samples')
    ap.add_argument('--out', help='write the sampled ranges\' disassembly, with counts, here')
    ap.add_argument('--hot-blocks', help='write the sampled blocks\' disassembly, with counts, here')
    ap.add_argument('--op', help='sum the copies of what this note names, by instruction')
    ap.add_argument('--blocks-of', help='the samples of what this note names, by block')
    ap.add_argument('--classes', action='store_true', help="the JIT's samples by kind of code, and whether they load or store a stack slot")
    ap.add_argument('--footprint', action='store_true', help="the 64-byte lines holding the JIT's sampled code: how many hold each share of its samples, and the span they cover")
    ap.add_argument('--top', type=int, default=25)
    args = ap.parse_args()

    ranges, insts = read_disasm(args.disasm)
    starts = [a for a, _, _, _ in insts]
    counts, native = Counter(), Counter()
    total = 0
    for line in open(args.samples):
        fields = line.split(None, 1)
        if not fields:
            continue
        total += 1
        ip = int(fields[0], 16)
        i = bisect_right(starts, ip) - 1
        if i >= 0:
            addr, r, _, _ = insts[i]
            base, size, _ = ranges[r]
            if base <= ip < base + size:
                counts[i] += 1
                continue
        native[fields[1].strip() if len(fields) > 1 else '[unknown]'] += 1
    jit = sum(counts.values())
    if not total:
        sys.exit(f'{args.samples}: no samples')
    print(f'{total} samples: {jit} ({100 * jit / total:.1f}%) in JIT code')
    for sym, n in native.most_common(args.top // 2):
        print(f'  {n:7} {100 * n / total:5.1f}%  {sym}')

    by_kind = Counter()
    for i, n in counts.items():
        notes = insts[i][3]
        by_kind[' / '.join(kind(n) for n in notes[1:]) or kind(notes[0]) if notes else '(no note)'] += n
    if args.footprint:
        # The hot code's lines, hottest first: how many a loop's code takes in the op cache and
        # instruction cache, which the same code laid out apart takes more of.
        lines = Counter()
        for i, n in counts.items():
            lines[insts[i][0] // 64] += n
        hottest = [line for line, _ in lines.most_common()]
        print(f'\nJIT code footprint: {len(lines)} 64-byte lines sampled')
        for share in (0.5, 0.8, 0.9, 0.95, 0.99):
            run, taken = 0, []
            for line in hottest:
                if run >= share * jit:
                    break
                run += lines[line]
                taken.append(line)
            print(f'  {int(share * 100):3}% of samples: {len(taken):5} lines, spanning {(max(taken) - min(taken) + 1) * 64:7} bytes')

    print(f'\nJIT samples by what emitted the code (summed over copies):')
    for k, n in by_kind.most_common(args.top):
        print(f'  {n:7} {100 * n / total:5.1f}%  {k}')

    by_block = Counter()
    for i, n in counts.items():
        block = next((note for note in insts[i][3] if note.startswith('block ')), '(no block)')
        by_block[block] += n
    print(f'\nJIT samples by block:')
    for k, n in by_block.most_common(args.top):
        print(f'  {n:7} {100 * n / total:5.1f}%  {k}')

    if args.classes:
        # Of the JIT's samples: what kind of code (a residual's group), and what the instruction
        # is: a stack slot's load or store (the window's traffic with the frame), a move between
        # registers (the window's shuffles into and out of a stencil's registers), one with the
        # pinned tag (boxing or unboxing a value), or anything else.
        classes = ['slot', 'move', 'tag', 'rest']
        by_class = Counter()
        ops = Counter()
        for i, n in counts.items():
            notes = insts[i][3]
            kinds = [kind(note) for note in notes[1:]] or [kind(notes[0])] if notes else ['(no note)']
            group = next((GROUPS[k] for k in reversed(kinds) if k in GROUPS), None)
            if group is None:
                group = 'op' if kinds[0].startswith(('window(', 'emit(')) else 'other'
            text = INST.match(insts[i][2]).group(3)
            what = 'slot' if SLOT.search(text) else 'move' if MOVE.search(text) else 'tag' if TAG.search(text) else 'rest'
            by_class[(group, what)] += n
            if group == 'op':
                ops[(kinds[0], what)] += n
        print(f'\nJIT samples by kind of code, and what the instruction is (of {jit}):')
        print(f'  {"":12} {"all":>6}' + ''.join(f'  {c:>6}' for c in classes))
        for group in ['op', 'guard', 'control', 'call/frame', 'region', 'other']:
            row = [by_class[(group, c)] for c in classes]
            if sum(row):
                print(f'  {group:12} {100 * sum(row) / jit:5.1f}%' + ''.join(f'  {100 * n / jit:5.1f}%' for n in row))
        print(f'\nWindow ops, by op:')
        names = Counter()
        for (op, _), n in ops.items():
            names[op] += n
        for op, n in names.most_common(args.top):
            print(f'  {op:28} {100 * n / jit:5.1f}%' + ''.join(f'  {100 * ops[(op, c)] / jit:5.1f}%' for c in classes))

    if args.blocks_of:
        of = Counter()
        for i, n in counts.items():
            notes = insts[i][3]
            if notes and args.blocks_of in notes[-1]:
                of[next((note for note in notes if note.startswith('block ')), '(no block)')] += n
        print(f'\n{args.blocks_of}: {sum(of.values())} samples, by block:')
        for k, n in of.most_common(args.top):
            print(f'  {n:7} {100 * n / total:5.1f}%  {k}')

    if args.op:
        # A copy is a run of instructions under one note naming `op`; copies of
        # the same code (the same instructions, but for their displacements)
        # are summed together, and each other code apart.
        runs = []
        prev = None
        for i, (addr, r, line, notes) in enumerate(insts):
            under = notes and args.op in notes[-1]
            key = (r, notes) if under else None
            if under and key != prev:
                runs.append([])
            prev = key
            if under:
                runs[-1].append(i)
        variants = {}
        for run in runs:
            texts = [INST.match(insts[i][2]).group(3).split(None, 1) for i in run]
            shape = tuple(t[1].split()[0] if len(t) > 1 else t[0] for t in texts)
            copies, by_offset, text = variants.setdefault(shape, [0, defaultdict(int), {}])
            variants[shape][0] += 1
            start = insts[run[0]][0]
            for i, t in zip(run, texts):
                off = insts[i][0] - start
                by_offset[off] += counts.get(i, 0)
                text.setdefault(off, ' '.join(t))
        ordered = sorted(variants.values(), key=lambda v: -sum(v[1].values()))
        for copies, by_offset, text in ordered:
            n = sum(by_offset.values())
            print(f'\n{args.op}: {len(by_offset)} instructions, {copies} copies, {n} samples ({100 * n / total:.1f}%)')
            for off in sorted(by_offset):
                print(f'  {by_offset[off]:7} +{off:<4x} {text[off]}')

    if args.hot_blocks:
        block_of = lambda notes: next((note for note in notes if note.startswith('block ')), None)
        hot = Counter()
        for i, n in counts.items():
            hot[(insts[i][1], block_of(insts[i][3]))] += n
        by_range = Counter()
        for (r, _), n in hot.items():
            by_range[r] += n
        with open(args.hot_blocks, 'w') as out:
            last_notes, last_block, last_range = None, None, None
            for i, (addr, r, line, notes) in enumerate(insts):
                block = (r, block_of(notes))
                if block[1] is None or not hot[block]:
                    last_block = None
                    continue
                if r != last_range:
                    base, size, title = ranges[r]
                    out.write(f'\n==== {title} @ {base:#x}, {size} bytes: {by_range[r]} samples\n')
                    last_range = r
                if block != last_block:
                    out.write(f'\n{hot[block]:7} samples: {block[1]}\n')
                    last_block, last_notes = block, tuple(n for n in notes if not n.startswith('block '))[:0]
                inner = tuple(n for n in notes if n != block[1] and not RANGE.match(n))
                inner = inner[next((k for k, n in enumerate(notes) if n == block[1]), 0):]
                shared = next((k for k, (a, b) in enumerate(zip(last_notes, inner)) if a != b), min(len(last_notes), len(inner)))
                for note in inner[shared:]:
                    out.write(f'        ; {note}\n')
                last_notes = inner
                n = counts.get(i, 0)
                out.write(f'{n or "":>7} {line}\n')
        print(f'\n{args.hot_blocks}')

    if args.out:
        with open(args.out, 'w') as out:
            sampled = {insts[i][1] for i in counts}
            by_range = Counter()
            for i, n in counts.items():
                by_range[insts[i][1]] += n
            last_notes, last_range = None, None
            for i, (addr, r, line, notes) in enumerate(insts):
                if r not in sampled:
                    continue
                if r != last_range:
                    base, size, title = ranges[r]
                    out.write(f'\n==== {title} @ {base:#x}, {size} bytes: {by_range[r]} samples\n')
                    last_range, last_notes = r, ()
                shared = next((k for k, (a, b) in enumerate(zip(last_notes, notes)) if a != b), min(len(last_notes), len(notes)))
                for note in notes[shared:]:
                    out.write(f'        ; {note}\n')
                last_notes = notes
                n = counts.get(i, 0)
                out.write(f'{n or "":>7} {line}\n')
        print(f'\n{args.out}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
