#!/usr/bin/env python3
"""A profile's samples on the JIT's code, joined to its disassembly.

    tools/jit_samples.py JIT_DISASM SAMPLES [--out FILE] [--op NOTE] [--top N]

JIT_DISASM is the `jit_disasm.txt` a run writes (feature `jit_disasm`), and
SAMPLES that same run's samples, `perf script -F ip,sym` (a sample's address,
then its symbol), so the addresses agree: `just jit-profile` makes both. With
precise samples (IBS), a sample's address is the instruction that ran.

Prints the samples' split between the JIT's code and the binary's functions,
and the JIT's by what emitted the code (the disassembly's notes: a region's
entry and exit, and a block's residuals and the parts of one) summed over
every copy. `--out` writes the disassembly of every range with a sample, each
instruction with its count. `--op` sums the copies of what one note names
(`PushFrame`, `window(GetTableInteger`) instruction by instruction, which
copies of the same code are, and prints them with the first copy's text.
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


def kind(note):
    """What a note names, without what's particular to one copy: a residual's
    index and operands, a block's number."""
    note = INDEX.sub('', note)
    if note.startswith('block '):
        return 'block entry'
    if note.startswith('window('):
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
    ap.add_argument('--op', help='sum the copies of what this note names, by instruction')
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
    print(f'\nJIT samples by what emitted the code (summed over copies):')
    for k, n in by_kind.most_common(args.top):
        print(f'  {n:7} {100 * n / total:5.1f}%  {k}')

    if args.op:
        # A copy is a run of instructions under one note naming `op`.
        by_offset, text, copies = defaultdict(int), {}, 0
        prev = None
        start = None
        for i, (addr, r, line, notes) in enumerate(insts):
            under = notes and args.op in notes[-1]
            key = (r, notes) if under else None
            if under and key != prev:
                copies += 1
                start = addr
            prev = key
            if under:
                off = addr - start
                by_offset[off] += counts.get(i, 0)
                text.setdefault(off, INST.match(line).group(3))
        n = sum(by_offset.values())
        print(f'\n{args.op}: {copies} copies, {n} samples ({100 * n / total:.1f}%)')
        for off in sorted(by_offset):
            print(f'  {by_offset[off]:7} +{off:<4x} {text[off]}')

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
