"""Samples on the instructions of some residuals in a sampled disassembly (`just
jit-profile`'s working/jit_samples.txt), summed over their copies, by residual
and mnemonic: what a window's samples go to, its operation or the checks,
moves and boxing around it.

    tools/window_mnemonics.py working/jit_samples.txt [NAMES]

NAMES, comma separated, are windows' names (`IntegerRK`) or other residuals'
(`guard_dynamic`); the integer windows by default."""
import collections
import re
import sys

RESIDUAL = re.compile(r"\s*; \d+ (window\((\w+)[^)]*\)|\S.*)")
INSN = re.compile(r"\s*(\d*)\s+[0-9a-f]{8,}\s+\+[0-9a-f]+\s+[0-9a-f]+\s+(\S+)")
WINDOWS = set(sys.argv[2].split(',')) if len(sys.argv) > 2 else {'IntegerRK', 'IntegerRR', 'IntegerKR', 'MaskRK'}

by_window = collections.Counter()
by_mnemonic = collections.defaultdict(collections.Counter)
window = None
for line in open(sys.argv[1]):
    if line.lstrip().startswith('; block'):
        window = None
    elif m := RESIDUAL.match(line):
        name = m.group(2) or m.group(1).split('(')[0]
        window = name if name in WINDOWS else None
    elif window and (m := INSN.match(line)):
        n = int(m.group(1) or 0)
        by_window[window] += n
        by_mnemonic[window][m.group(2)] += n
for window, total in by_window.most_common():
    print(f"{window}: {total}")
    for mnemonic, n in by_mnemonic[window].most_common(14):
        print(f"    {n:5} {mnemonic}")
