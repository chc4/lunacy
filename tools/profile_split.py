#!/usr/bin/env python3
"""Where a profile's time goes, each sample counted once: from `perf script`
stacks of a run recorded with call graphs (`just flamegraph`, working/perf.data),
whether its leaf is JIT code (a `jit_block_` symbol from the perf map), its
stack has JIT code but its leaf is the runtime's (a native, a helper), or no JIT
code is on its stack: then by the outermost of the specializer's phases on it
(compiling, contracting, forcing a thunk) or the collector, else the
interpreter. The leaf functions of each split's samples follow.

    profile_split.py [working/perf.data] [--top N]
"""
import argparse
import collections
import subprocess

# The specializer's phases, by a function on the stack, the first that matches
# naming the sample's.
PHASES = [
    ('trim (unreachable sweep)', 'Specializer>::trim'),
    ('contract (rebuilding origins)', 'Specializer>::rebuild_queued'),
    ('contract (other)', 'Specializer>::contract'),
    ('jit compile', 'Specializer>::jit_compile'),
    ('compile (versions)', 'Specializer>::compile'),
    ('compile (versions)', 'Specializer>::block'),
    ('thunk forcing', 'make_'),
    ('gc', 'gc::Heap'),
]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('data', nargs='?', default='working/perf.data')
    ap.add_argument('--top', type=int, default=8)
    args = ap.parse_args()
    script = subprocess.run(['perf', 'script', '-i', args.data, '-F', 'ip,sym', '--no-inline'],
                            capture_output=True, text=True, check=True).stdout
    splits = collections.Counter()
    leaves = collections.defaultdict(collections.Counter)
    total = 0
    for sample in script.strip().split('\n\n'):
        frames = [line.strip().split(None, 1) for line in sample.splitlines() if line.strip()]
        syms = [frame[1] if len(frame) > 1 else frame[0] for frame in frames]
        if not syms:
            continue
        total += 1
        leaf = syms[0]
        if leaf.startswith('jit_block_'):
            split = 'in JIT code'
        elif any(sym.startswith('jit_block_') for sym in syms):
            split = 'under JIT code, in the runtime'
        else:
            split = next((name for name, sym in PHASES if any(sym in s for s in syms)), 'interpreter and the rest')
        splits[split] += 1
        leaves[split][leaf[:110]] += 1
    print(f'{total} samples')
    for split, n in splits.most_common():
        print(f'{n:>7} {100 * n / total:5.1f}%  {split}')
        for leaf, m in leaves[split].most_common(args.top):
            print(f'          {m:>6} {100 * m / total:5.1f}%  {leaf}')


if __name__ == '__main__':
    main()
