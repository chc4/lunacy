#!/usr/bin/env python3
"""Compare the residual graphs (`func_<line>.dot`, feature `graph`) of two runs.

Every dump holds all of the program's blocks, but labels only its function's
with their version (`PC: SubPc(..)`). So the program's blocks, the blocks
entered at least once, and the residuals in them come from any one dump; per
function come its versioned blocks and the pc with the most (the blocks
starting at it or inside its instruction). `just graph-guards` runs this on a
benchmark with and without dynamic guards.

    tools/graph_blocks.py DIR_A DIR_B
"""
import re
import sys
from collections import Counter
from pathlib import Path

# A block's node label: `"<id> x<entered> | { PC: SubPc(<pc>, <path>)\n... | r1| r2 }"`,
# the PC part only on blocks with a version in the dump's function.
NODE = re.compile(r'label="(\d+) x(\d+) \| \{ (.*?) \}"')
PC = re.compile(r'PC: SubPc\((\d+), (\d+)\)')


def stats(path):
    blocks = entered = residuals = 0
    pcs = Counter()
    for match in NODE.finditer(path.read_text()):
        blocks += 1
        entered += int(match.group(2)) > 0
        body = match.group(3)
        pc = PC.search(body)
        if pc:
            pcs[int(pc.group(1))] += 1
            residuals += body.count('|')  # the context is the first field
        else:
            residuals += body.count('|') + 1
    return (blocks, entered, residuals), pcs


def worst(pcs):
    if not pcs:
        return '-'
    pc, count = max(pcs.items(), key=lambda item: (item[1], -item[0]))
    return f'{count} (pc {pc})'


def main(a, b):
    a, b = Path(a), Path(b)
    key = lambda n: int(re.search(r'\d+', n).group())
    names = sorted({p.name for p in a.glob('func_*.dot')} | {p.name for p in b.glob('func_*.dot')}, key=key)
    if not names:
        sys.exit(f'no func_*.dot in {a} or {b}')
    runs = [{name: stats(d / name) for name in names if (d / name).exists()} for d in (a, b)]
    print(f'{a.name} / {b.name}\n')
    print('program | blocks | entered | residuals')
    print('--- | --- | --- | ---')
    (pa, _), (pb, _) = (next(iter(run.values())) for run in runs)
    print(' | '.join(['all'] + [f'{x} / {y}' for x, y in zip(pa, pb)]))
    print('\nfunction | versioned blocks | most at one pc')
    print('--- | --- | ---')
    for name in names:
        pcs = [run[name][1] if name in run else Counter() for run in runs]
        print(f'{name.removesuffix(".dot")} | {sum(pcs[0].values())} / {sum(pcs[1].values())} | {worst(pcs[0])} / {worst(pcs[1])}')


if __name__ == '__main__':
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2])
