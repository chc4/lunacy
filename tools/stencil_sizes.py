#!/usr/bin/env python3
"""The size of every window op's stencil in a binary.

Each `windowed!` op is compiled to one stencil per `SKIP`; this reads the
`SKIP` 0 one of each (`<Op<...>>::__stencil::<0>`). A stencil's size is its
function's: its bytes, from the symbol table, and the instructions in them.
Alongside it, what the copier (`window::stencil_body`) copies of it: a final
jump to the op's continuation (`__next`) is sliced off, and a stencil not
ending in one is copied whole with a `ud2` after it. Stencils are listed
biggest first, by instructions.

    tools/stencil_sizes.py target/release/bench [target/unsafe/bench]

(after building target/jit_disasm/release/demangle, as `just stencil-sizes` does)
"""
import re
import subprocess
import sys

HEADER = re.compile(r'^([0-9a-f]+) <(.*)>:$')
INSTRUCTION = re.compile(r'^\s+([0-9a-f]+):\s+(\S.*)$')
STENCIL = re.compile(r'^<(.*)>::__stencil::<0>$')
DEMANGLE = 'target/jit_disasm/release/demangle'


def demangled(args):
    # Demangled by the `demangle` bin (rustc-demangle), not objdump's -C, which
    # can't demangle v0 symbols with enum const generics (`NumericRR<{Opcode::ADD}, ..>`).
    raw = subprocess.run(['objdump'] + args, capture_output=True, check=True).stdout
    return subprocess.run([DEMANGLE], input=raw, capture_output=True, check=True).stdout.decode()


def sizes(binary):
    """{function address: size in bytes}, from the symbol table."""
    found = {}
    for line in demangled(['-t', binary]).splitlines():
        fields = line.split()
        if len(fields) >= 6 and fields[2] == 'F':
            found[int(fields[0], 16)] = int(fields[4], 16)
    return found


def stencils(binary):
    """{op: (bytes, instructions, instructions copied)} over the stencils in `binary`."""
    size_of = sizes(binary)
    found, op, start, code = {}, None, 0, []

    def done():
        if op is None:
            return
        size = size_of.get(start, 0)
        insts = [inst for at, inst in code if at < start + size]
        final_become = bool(insts) and insts[-1].startswith('jmp') and '__next>' in insts[-1]
        found[op] = (size, len(insts), len(insts) - 1 if final_become else len(insts) + 1)

    for line in demangled(['-d', '--no-show-raw-insn', binary]).splitlines():
        m = HEADER.match(line)
        if m:
            done()
            s = STENCIL.match(m.group(2))
            op, start, code = (s.group(1) if s else None), int(m.group(1), 16), []
            continue
        m = INSTRUCTION.match(line)
        if m and op is not None:
            code.append((int(m.group(1), 16), m.group(2)))
    done()
    return found


def main():
    binaries = sys.argv[1:]
    found = [stencils(b) for b in binaries]
    ops = sorted({op for f in found for op in f}, key=lambda op: -max(f.get(op, (0, 0, 0))[1] for f in found))
    width = max(len(op) for op in ops) if ops else 10
    print('%-*s' % (width, 'op') + ''.join('%32s' % ('bytes insts copied (%s)' % b.split('/')[-2]) for b in binaries))
    for op in ops:
        print('%-*s' % (width, op) + ''.join('%32s' % ('%d %d %d' % f[op] if op in f else '-') for f in found))
    # Totals over each binary's stencils, and over those every binary has.
    common = [op for op in ops if all(op in f for f in found)]
    for label, among in (('total', None), ('total (in every binary)', common)):
        sums = [tuple(sum(f[op][i] for op in (among if among is not None else f)) for i in range(3)) for f in found]
        print('%-*s' % (width, label) + ''.join('%32s' % ('%d %d %d' % s) for s in sums))


if __name__ == '__main__':
    main()
