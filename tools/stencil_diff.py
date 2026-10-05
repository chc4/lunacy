#!/usr/bin/env python3
"""Whether two builds compile the window ops' stencils to the same code: each
op's `SKIP` 0 stencil (as `stencil_cold.py` finds them) in binary A and in B,
compared instruction by instruction with addresses taken out: a jump inside a
stencil by its offset in it, a jump or call out of it by the symbol it names,
and data (RIP-relative operands, thread-locals) not at all, as it's laid out
differently in each binary. Prints how many are the same, how many that
differ change length and the instructions in each binary, those that change
length by how much, the stencils whose size in bytes changes and by how much
(most grown first), and each that differs with its first difference.

    tools/stencil_diff.py A B [--show N]

(after building target/jit_disasm/release/demangle, as `just stencil-cold` does)
"""
import argparse
import re
import sys

sys.path.insert(0, 'tools')
from stencil_cold import stencils, symbol_sizes

# A branch target: an address and the symbol it's in.
TARGET = re.compile(r'\b([0-9a-f]+) <([^>]*)>')
# A RIP-relative operand's comment: `# address <symbol>`.
COMMENT = re.compile(r'\s*#.*$')
DISPLACEMENT = re.compile(r'-?0x[0-9a-f]+\(%rip\)')
THREAD_LOCAL = re.compile(r'%fs:-?0x[0-9a-f]+')


def normalized(code):
    """The stencil's instructions with its addresses taken out."""
    start = code[0][0] if code else 0
    end = code[-1][0] if code else 0
    out = []
    for _, mnem, ops in code:
        def target(m):
            addr = int(m.group(1), 16)
            return f'+{addr - start:#x}' if start <= addr <= end else f'<{m.group(2)}>'
        ops = TARGET.sub(target, ops)
        ops = COMMENT.sub('', ops)
        ops = DISPLACEMENT.sub('(%rip)', ops)
        ops = THREAD_LOCAL.sub('%fs:(tls)', ops)
        out.append(f'{mnem} {ops}'.strip())
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('a')
    ap.add_argument('b')
    ap.add_argument('--show', type=int, default=20, help='how many differing stencils to list')
    args = ap.parse_args()

    size_a, size_b = symbol_sizes(args.a), symbol_sizes(args.b)
    a, b = stencils(args.a, size_a), stencils(args.b, size_b)
    both = sorted(set(a) & set(b))
    bytes_a = {op: size_a.get(a[op][0][0], 0) for op in both if a[op]}
    bytes_b = {op: size_b.get(b[op][0][0], 0) for op in both if b[op]}
    differ = []
    for op in both:
        x, y = normalized(a[op]), normalized(b[op])
        if x != y:
            at = next((i for i, (p, q) in enumerate(zip(x, y)) if p != q), min(len(x), len(y)))
            differ.append((op, len(x), len(y), at, x[at] if at < len(x) else '(end)', y[at] if at < len(y) else '(end)'))
    print(f'{len(both) - len(differ)} of {len(both)} stencils the same; '
          f'{len(set(a) - set(b))} only in A, {len(set(b) - set(a))} only in B')
    # Of those that differ, the ones whose length changed, most grown first.
    grown = sorted((d for d in differ if d[1] != d[2]), key=lambda d: d[1] - d[2])
    print(f'{len(differ) - len(grown)} differ at the same length; {len(grown)} change length, '
          f'{sum(len(normalized(a[op])) for op in both)} instructions in A, '
          f'{sum(len(normalized(b[op])) for op in both)} in B')
    for op, nx, ny, *_ in grown[:args.show]:
        print(f'  {ny - nx:+4} ({nx} -> {ny}) {op}')
    resized = sorted((op for op in bytes_a if op in bytes_b and bytes_a[op] != bytes_b[op]),
                     key=lambda op: bytes_a[op] - bytes_b[op])
    print(f'{len(resized)} change size in bytes, {sum(bytes_a.values())} bytes in A, {sum(bytes_b.values())} in B')
    for op in resized[:args.show]:
        print(f'  {bytes_b[op] - bytes_a[op]:+5} bytes ({bytes_a[op]} -> {bytes_b[op]}) {op}')
    for op, nx, ny, at, x, y in differ[:args.show]:
        print(f'\n{op}: {nx} instructions in A, {ny} in B; first difference at {at}')
        print(f'  A: {x}')
        print(f'  B: {y}')
    return 1 if differ else 0


if __name__ == '__main__':
    sys.exit(main())
