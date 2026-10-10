#!/usr/bin/env python3
"""JIT code bytes by the function chain its blocks are in, and by the residual kind that emitted
them, from `just jit-disasm` dumps whose block notes name their functions (`725-693`), compared
between two dumps.

    tools/chain_bytes.py base/jit_disasm.txt head/jit_disasm.txt
"""
import collections, re, sys

BLOCK = re.compile(r"\s*; block \d+ \(pc \d+, function ([\d?-]+)")
RESIDUAL = re.compile(r"\s*;\s+\d+ (\w+)")
INSTR = re.compile(r"\s*[0-9a-f]{8,} \+([0-9a-f]+)\s+([0-9a-f]+)\s")


def tally(path):
    """(chain bytes, residual-kind bytes) of a dump."""
    chains, kinds = collections.Counter(), collections.Counter()
    chain, kind = "(region)", "(region)"
    for line in open(path):
        if line.startswith("===="):
            chain, kind = "(region)", "(region)"
        elif m := BLOCK.match(line):
            chain, kind = m.group(1), "(block entry)"
        elif m := RESIDUAL.match(line):
            kind = m.group(1)
        elif m := INSTR.match(line):
            size = len(m.group(2)) // 2
            chains[chain] += size
            kinds[kind] += size
    return chains, kinds


def compare(title, base, head, top=14):
    print(f"== {title}")
    for key in sorted(set(base) | set(head), key=lambda k: -abs(head[k] - base[k]))[:top]:
        print(f"  {key[:30]:30} {base[key]:>8} {head[key]:>8} {head[key] - base[key]:>+8}")


base, head = tally(sys.argv[1]), tally(sys.argv[2])
compare("bytes by function chain", base[0], head[0])
compare("bytes by residual", base[1], head[1])
