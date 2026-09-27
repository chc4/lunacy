#!/usr/bin/env python3
"""Where the integer and double encodings meet in residual graphs (`func_*.dot`,
feature `graph`): per function,

  * encoding splits: the pcs whose versions' contexts differ only in slots one
    types `integer` and another `double` (or `number`), and in which slots;
  * encoding guards: `guard(slot, integer|double)` residuals, weighted by their
    blocks' entry counts (the `xN` of each block's label);
  * arithmetic: the integer (`Integer*`, `Fits*`), double (`Numeric*`) and
    compare window ops, weighted the same way.

    tools/graph_encodings.py target/graphs/<benchmark>/current [--top N]
"""
import argparse
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

NODE = re.compile(r'^\s*(\d+)\[id=\d+,shape=record,label="\d+ x(\d+) \| \{ (.*) \}"\]\s*$')
KEY = re.compile(r'PC: SubPc\((\d+), (\d+)\)\\ncontext\(\[([^\]]*)\]')
NUMBERS = {'integer', 'double', 'number'}


def blocks(path):
    """(block, runs, pc or None, types or None, residuals) of each block."""
    for line in open(path):
        m = NODE.match(line)
        if not m:
            continue
        block, runs, body = int(m.group(1)), int(m.group(2)), m.group(3)
        parts = [p.strip() for p in body.split('|')]
        key = KEY.search(parts[0])
        if key:
            pc, types = int(key.group(1)), key.group(3).split(',')
            parts = parts[1:]
        else:
            pc, types = None, None
        yield block, runs, pc, types, parts


def splits(found):
    """{pc: (versions, {slot: types seen})} of pcs versioned by encoding alone."""
    by_pc = defaultdict(list)
    for _, _, pc, types, _ in found:
        if pc is not None:
            by_pc[pc].append(types)
    out = {}
    for pc, contexts in by_pc.items():
        erased = defaultdict(list)
        for types in contexts:
            erased[tuple('number' if t in NUMBERS else t for t in types)].append(types)
        for group in erased.values():
            if len(group) < 2:
                continue
            slots = {}
            for slot in range(max(len(t) for t in group)):
                seen = {t[slot] for t in group if slot < len(t)}
                if len(seen) > 1:
                    slots[slot] = sorted(seen)
            if slots:
                out.setdefault(pc, []).append((len(group), slots))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('dir')
    ap.add_argument('--top', type=int, default=8)
    args = ap.parse_args()
    for path in sorted(Path(args.dir).glob('func_*.dot'), key=lambda p: int(p.stem.split('_')[1])):
        found = list(blocks(path))
        # Every dump holds all of the program's blocks, but labels only its
        # function's with their version (tools/graph_blocks.py).
        found = [b for b in found if b[2] is not None]
        guards, ops = Counter(), Counter()
        for _, runs, _, _, residuals in found:
            for r in residuals:
                g = re.match(r'guard\((\d+), (integer|double)\)', r)
                if g:
                    guards[f'guard({g.group(1)}, {g.group(2)})'] += runs
                w = re.match(r'window\((Integer\w+|Fits\w+|Numeric\w+|Compare\w+|ForLoop)', r)
                if w:
                    ops[w.group(1)] += runs
        split = splits(found)
        if not (guards or split):
            continue
        print(f'== {path.name}: {len(found)} versioned blocks')
        for pc in sorted(split):
            for versions, slots in split[pc]:
                print(f'  pc {pc}: {versions} versions differ only in ' + ', '.join(f'slot {s} {"/".join(t)}' for s, t in slots.items()))
        for guard, runs in guards.most_common(args.top):
            print(f'  {guard}: {runs} runs')
        print('  ops: ' + ', '.join(f'{op} {runs}' for op, runs in ops.most_common()))
    return 0


if __name__ == '__main__':
    sys.exit(main())
