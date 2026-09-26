#!/usr/bin/env python3
"""The size of every window op's stencil in a binary, in instructions.

Each `windowed!` op is compiled to one stencil per `SKIP`; this reads the
`SKIP` 0 one of each (`<Op<...>>::__stencil::<0>`) from `objdump -d`. A stencil
ends by jumping to its op's continuation (`__next`), which the copier slices
off: the instructions before that jump are the ones copied into JIT code and
run (`hot`), the ones after it (a panic path, say) are copied but never run
(`cold`). Stencils are listed biggest first, by hot instructions.

    tools/stencil_sizes.py target/release/bench [target/unsafe/bench]

(after building target/jit_disasm/release/demangle, as `just stencil-sizes` does)
"""
import re
import subprocess
import sys

HEADER = re.compile(r'^[0-9a-f]+ <(.*)>:$')
INSTRUCTION = re.compile(r'^\s+[0-9a-f]+:\s+(\S.*)$')
STENCIL = re.compile(r'^<(.*)>::__stencil::<0>$')
DEMANGLE = 'target/jit_disasm/release/demangle'


def stencils(binary):
    """{op: (hot, cold)} over the stencils in `binary`."""
    # Demangled by the `demangle` bin (rustc-demangle), not objdump's -C, which
    # can't demangle v0 symbols with enum const generics (`NumericRR<{Opcode::ADD}, ..>`).
    disassembly = subprocess.run(['objdump', '-d', '--no-show-raw-insn', binary], capture_output=True, check=True).stdout
    out = subprocess.run([DEMANGLE], input=disassembly, capture_output=True, check=True).stdout.decode()
    found, op, code = {}, None, []
    def done():
        if op is None:
            return
        tail = next((i for i, inst in enumerate(code) if inst.startswith('jmp') and '__next>' in inst), len(code))
        found[op] = (tail, max(len(code) - tail - 1, 0))
    for line in out.splitlines():
        m = HEADER.match(line)
        if m:
            done()
            s = STENCIL.match(m.group(1))
            op, code = (s.group(1) if s else None), []
            continue
        m = INSTRUCTION.match(line)
        if m and op is not None:
            code.append(m.group(1))
    done()
    return found


def main():
    binaries = sys.argv[1:]
    sizes = [stencils(b) for b in binaries]
    ops = sorted({op for s in sizes for op in s}, key=lambda op: -max(s.get(op, (0, 0))[0] for s in sizes))
    width = max(len(op) for op in ops) if ops else 10
    print('%-*s' % (width, 'op') + ''.join('%22s' % ('hot cold ' + b.split('/')[-2]) for b in binaries))
    for op in ops:
        print('%-*s' % (width, op) + ''.join('%22s' % ('%d %d' % s[op] if op in s else '-') for s in sizes))


if __name__ == '__main__':
    main()
