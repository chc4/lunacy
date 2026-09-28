#!/usr/bin/env python3
"""The size of every function in a binary whose demangled name matches a
regex: its bytes (from the symbol table), the instructions in them, and the
functions it calls. A library native's closure, for one, to compare with its
window op's stencil (`just stencil-sizes`).

    tools/symbol_sizes.py target/unsafe/bench 'library::globals::\\{closure#17\\}'

(after building target/jit_disasm/release/demangle, as `just stencil-asm` does)
"""
import re
import subprocess
import sys

HEADER = re.compile(r'^([0-9a-f]+) <(.*)>:$')
INSTRUCTION = re.compile(r'^\s+([0-9a-f]+):\s+(\S+)\s*(.*)$')
CALL_TARGET = re.compile(r'<([^>+]*(?:<[^>]*>[^>+]*)*)(?:\+0x[0-9a-f]+)?>')
DEMANGLE = 'target/jit_disasm/release/demangle'


def demangled(args):
    raw = subprocess.run(['objdump'] + args, capture_output=True, check=True).stdout
    return subprocess.run([DEMANGLE], input=raw, capture_output=True, check=True).stdout.decode()


def main():
    binary, pattern = sys.argv[1], re.compile(sys.argv[2])
    size_of = {}
    for line in demangled(['-t', binary]).splitlines():
        fields = line.split()
        if len(fields) >= 6 and fields[2] == 'F':
            size_of[int(fields[0], 16)] = int(fields[4], 16)
    name, start, insts, calls = None, 0, 0, []

    def done():
        if name is not None:
            print('%6d bytes %4d insts  %s' % (size_of.get(start, 0), insts, name))
            for target in sorted(set(calls)):
                print('        calls %s' % target)

    for line in demangled(['-d', '--no-show-raw-insn', binary]).splitlines():
        m = HEADER.match(line)
        if m:
            done()
            name = m.group(2) if pattern.search(m.group(2)) else None
            start, insts, calls = int(m.group(1), 16), 0, []
            continue
        m = INSTRUCTION.match(line)
        if m and name is not None and int(m.group(1), 16) < start + size_of.get(start, 0):
            insts += 1
            if m.group(2) == 'call':
                t = CALL_TARGET.search(m.group(3))
                calls.append(t.group(1) if t else m.group(3).split('#')[-1].strip())
    done()


if __name__ == '__main__':
    main()
