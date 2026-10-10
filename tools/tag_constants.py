#!/usr/bin/env python3
"""Where JIT code materializes the pinned tag, `LBoxed::NUMBER_TAG` (0xfffe000000000000),
instead of using r14: each instruction in a `just jit-disasm` dump whose immediate (which
the disassembler prints signed, `-0x2000000000000`) or pool entry is the tag, counted by the
note of the residual (or region code) that emitted it, with one example of each.

    tools/tag_constants.py working/jit_disasm.txt
"""
import collections, re, sys

TAG = re.compile(r'0xfffe000000000000\b|-0x2000000000000\b')
NOTE = re.compile(r'\s*;\s+(?:\d+\s+)?(.*)')
INSTR = re.compile(r'\s*[0-9a-f]{8,} \+[0-9a-f]+\s+[0-9a-f]+\s+(.*)')

counts, examples = collections.Counter(), {}
note = '(region code)'
for line in open(sys.argv[1]):
    if line.startswith('===='):
        note = '(region code)'
    elif (m := INSTR.match(line)) and TAG.search(line):
        # A residual's kind, and a window op's name: `window(NumericRR)`.
        name = re.match(r'[^(,]*(?:\(\w+)?', note).group(0) + (')' if '(' in note else '')
        counts[name] += 1
        examples.setdefault(name, m.group(1).strip())
    elif (m := NOTE.match(line)) and not INSTR.match(line):
        note = m.group(1)
for name, n in counts.most_common():
    print(f'{n:>6}  {name:<28} {examples[name]}')
print(f'{sum(counts.values()):>6}  total')
