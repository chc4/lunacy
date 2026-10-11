#!/usr/bin/env python3
"""The blocks of one function chain (`725-693`) in a `just jit-disasm` dump: each block's header and
its residual notes, with the bytes each residual emitted, so two dumps' code for an inlined callee
can be read side by side.

    tools/chain_blocks.py working/jit_disasm.txt 65-259
"""
import re, sys

BLOCK = re.compile(r"\s*; block \d+ \(pc \d+, function ([\d?-]+)")
OTHER_BLOCK = re.compile(r"\s*; block |  ; (into a cold stencil|an exit's way|site record of|exit_jit|constant pool|region entry|load the entry window)")
RESIDUAL = re.compile(r"\s*;\s+\d+ \w+")
INSTR = re.compile(r"\s*[0-9a-f]{8,} \+([0-9a-f]+)\s+([0-9a-f]+)\s")

path, chain = sys.argv[1], sys.argv[2]
inside, note, size = False, None, 0


def flush():
    if note is not None:
        print(f"    {size:>5}  {note}")


for line in open(path):
    if m := BLOCK.match(line):
        flush()
        note, size = None, 0
        inside = m.group(1) == chain
        if inside:
            print(line.strip()[2:])
    elif line.startswith("====") or OTHER_BLOCK.match(line):
        flush()
        note, size, inside = None, 0, False
    elif inside and RESIDUAL.match(line):
        flush()
        note, size = line.strip()[2:].strip(), 0
    elif inside and (m := INSTR.match(line)):
        size += len(m.group(2)) // 2
flush()
