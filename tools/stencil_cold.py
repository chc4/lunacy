#!/usr/bin/env python3
"""Cold code in every window op's stencil, and the stencils' assembly.

For each stencil (the `SKIP` 0 one of each op, `<Op<...>>::__stencil::<0>`,
its instructions bounded by its symbol size), this builds its control flow
graph: basic blocks, with edges for jumps, conditional jumps and falling
through. A call to a function that never returns (one named `panic...`) or a
trap (`ud2`, `int3`) ends its block with no successor. The stencil's tailcall is
its jump to its op's continuation (`__next`). Then, per stencil:

  cold      blocks from which no tailcall can be reached: panics and traps;
  above     cold blocks at a lower address than a tailcall;
  rejoins   blocks at a higher address than a tailcall jumping to a block at a
            lower address than it: out-of-line code jumping back up into the
            path to the tailcall;
  calls     calls that return, and what they call: slow paths in the stencil,
            copied with every copy of it, rather than in its cold stencil.

It prints how many stencils have each, and lists them. With `--dump FILE`, it
also writes every stencil's assembly to FILE.

    tools/stencil_cold.py target/release/bench [--dump stencils.s]

(after building target/jit_disasm/release/demangle, as `just stencil-cold` does)
"""
import argparse
import re
import subprocess

HEADER = re.compile(r'^([0-9a-f]+) <(.*)>:$')
INSTRUCTION = re.compile(r'^\s+([0-9a-f]+):\s+(\S+)\s*(.*)$')
STENCIL = re.compile(r'^<(.*)>::__stencil::<0>$')
TARGET = re.compile(r'^([0-9a-f]+)(?:\s+<(.*)>)?$')
DEMANGLE = 'target/jit_disasm/release/demangle'


def demangled(args):
    raw = subprocess.run(['objdump'] + args, capture_output=True, check=True).stdout
    return subprocess.run([DEMANGLE], input=raw, capture_output=True, check=True).stdout.decode()


def symbol_sizes(binary):
    """{address: size in bytes} over the functions in `binary`."""
    size_of = {}
    for line in demangled(['-t', binary]).splitlines():
        fields = line.split()
        if len(fields) >= 6 and fields[2] == 'F':
            size_of[int(fields[0], 16)] = int(fields[4], 16)
    return size_of


def stencils(binary, size_of=None):
    """{op: [(address, mnemonic, operands)]} over the stencils in `binary`."""
    if size_of is None:
        size_of = symbol_sizes(binary)
    found, op, start = {}, None, 0
    for line in demangled(['-d', '--no-show-raw-insn', binary]).splitlines():
        m = HEADER.match(line)
        if m:
            s = STENCIL.match(m.group(2))
            op, start = (s.group(1) if s else None), int(m.group(1), 16)
            if op is not None:
                found[op] = []
            continue
        m = INSTRUCTION.match(line)
        if m and op is not None and int(m.group(1), 16) < start + size_of.get(start, 0):
            found[op].append((int(m.group(1), 16), m.group(2), m.group(3)))
    return found


def analyse(code):
    """(cold block addresses, those above a tailcall, rejoining block addresses)."""
    if not code:
        return [], [], []
    addrs = {a for a, _, _ in code}

    def target(operands):
        m = TARGET.match(operands.strip())
        return (int(m.group(1), 16), m.group(2) or '') if m else (None, '')

    # Block leaders: the entry, jump targets inside, and whatever follows a
    # jump, a trap or a call that never returns.
    leaders = {code[0][0]}
    ends = {}
    for i, (addr, mnem, ops) in enumerate(code):
        nxt = code[i + 1][0] if i + 1 < len(code) else None
        if mnem.startswith('j'):
            t, name = target(ops)
            if t in addrs:
                leaders.add(t)
            if nxt is not None:
                leaders.add(nxt)
        elif mnem in ('ud2', 'int3', 'ret') or (mnem == 'call' and 'panic' in ops):
            if nxt is not None:
                leaders.add(nxt)
    # Blocks: (start, [instructions]) in address order.
    blocks, current = [], None
    for inst in code:
        if inst[0] in leaders:
            current = [inst[0], []]
            blocks.append(current)
        current[1].append(inst)
    starts = [b[0] for b in blocks]
    succs, tail = {}, {}
    tailcalls = []
    for bi, (start, insts) in enumerate(blocks):
        addr, mnem, ops = insts[-1]
        fall = starts[bi + 1] if bi + 1 < len(blocks) else None
        out, is_tail = [], False
        if mnem.startswith('j'):
            t, name = target(ops)
            if '__next' in name or '__next>' in ops:
                is_tail = True
                tailcalls.append(addr)
            elif t in addrs:
                out.append(t)
            if mnem != 'jmp' and fall is not None:
                out.append(fall)
        elif mnem in ('ud2', 'int3', 'ret') or (mnem == 'call' and 'panic' in ops):
            pass
        elif fall is not None:
            out.append(fall)
        succs[start], tail[start] = out, is_tail
    # Blocks from which a tailcall can be reached.
    reaches = {s for s in starts if tail[s]}
    changed = True
    while changed:
        changed = False
        for s in starts:
            if s not in reaches and any(t in reaches for t in succs[s]):
                reaches.add(s)
                changed = True
    cold = [s for s in starts if s not in reaches]
    above = [s for s in cold if any(t > s for t in tailcalls)]
    rejoins = [s for s in starts if any(t < s and any(u < t for u in succs[s]) for t in tailcalls)]
    return cold, above, rejoins


def calls(code):
    """The functions a stencil calls that return: its slow paths copied into
    every copy of it, with what the call keeps of the window around it."""
    out = []
    for _, mnem, ops in code:
        if mnem == 'call' and 'panic' not in ops:
            m = TARGET.match(ops.strip())
            out.append(m.group(2) if m and m.group(2) else ops.strip())
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('binary')
    parser.add_argument('--dump', help="write every stencil's assembly here")
    args = parser.parse_args()
    found = stencils(args.binary)
    if args.dump:
        with open(args.dump, 'w') as out:
            for op in sorted(found):
                out.write('<%s>::__stencil::<0>:\n' % op)
                for addr, mnem, ops in found[op]:
                    out.write('  %x:\t%s %s\n' % (addr, mnem, ops))
                out.write('\n')
    results = {op: analyse(code) for op, code in found.items()}
    for i, name in enumerate(['cold', 'above', 'rejoins']):
        having = sorted(op for op, r in results.items() if r[i])
        print('%s: %d of %d stencils' % (name, len(having), len(found)))
        for op in having:
            print('    %s' % op)
    calling = sorted((op, calls(code), len(code)) for op, code in found.items() if calls(code))
    print('calls: %d of %d stencils' % (len(calling), len(found)))
    for op, callees, size in calling:
        print('    %s (%d instructions): %s' % (op, size, ', '.join(callees)))


if __name__ == '__main__':
    main()
