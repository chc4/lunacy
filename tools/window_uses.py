"""What reads the integer windows' results, in a sampled disassembly (`just
jit-profile`'s working/jit_samples.txt): for each window writing an integer, the
first residual after it, in the code's order, reading the slot it wrote, before
the slot is written again, and as what (an integer window's operand, a table
access's key, a stored value, ...), weighted by the window's samples. Whether a
result could stay unboxed, read only as an integer, or is needed boxed.

    tools/window_uses.py working/jit_samples.txt
"""
import collections
import re
import sys

RESIDUAL = re.compile(r"\s*; \d+ (.*)$")
INSN = re.compile(r"\s*(\d*)\s+[0-9a-f]{8,}\s+\+[0-9a-f]+\s+[0-9a-f]+\s+(.*)$")
INTEGER = {'IntegerRK', 'IntegerRR', 'IntegerKR', 'MaskRK', 'FloorShiftK'}
# Each residual's operands that are read as integers only: by position among
# its numeric arguments (the `out` slot apart).
AS_INTEGER = {
    'IntegerRK': 'arith', 'IntegerRR': 'arith', 'IntegerKR': 'arith', 'MaskRK': 'arith', 'FloorShiftK': 'arith',
}
KEYED = {'GetTableInteger': 1, 'SetTableInteger': 1, 'guard_dynamic(InArray': 1}


def parse(text):
    """(name, slots read, slot written) of a residual's text."""
    m = re.match(r"window\((\w+)((?:, [^)]*)?)\)", text)
    if m:
        name, args = m.group(1), m.group(2)
    else:
        m = re.match(r"(\w+)\(([^)]*)\)", text)
        if not m:
            return text.split()[0] if text else '', [], None
        name, args = m.group(1), ', ' + m.group(2)
        if name == 'guard_dynamic':
            parts = [a.strip() for a in args.split(',') if a.strip()]
            name = f"guard_dynamic({parts[0]}"
            args = ', ' + ', '.join(parts[1:])
    out = None
    reads = []
    for arg in [a.strip() for a in args.split(',') if a.strip()]:
        if arg.startswith('out '):
            out = int(arg[4:])
        elif re.fullmatch(r'\d+', arg):
            reads.append(int(arg))
    return name, reads, out


def main():
    stream = []  # (name, reads, out, samples)
    stores = collections.Counter()
    for line in open(sys.argv[1]):
        if line.lstrip().startswith('; block'):
            continue
        if m := RESIDUAL.match(line):
            stream.append(list(parse(m.group(1))) + [0])
        elif (m := INSN.match(line)) and stream:
            n = int(m.group(1) or 0)
            stream[-1][3] += n
            if re.match(r"mov qword \[r13 \+", m.group(2)):
                stores['value stack store'] += n
            stores['all'] += n
    uses = collections.Counter()
    for i, (name, reads, out, samples) in enumerate(stream):
        if name not in INTEGER or out is None:
            continue
        use = 'none before it is overwritten or the stream ends'
        for later, later_reads, later_out, _ in stream[i + 1:i + 40]:
            if out in later_reads:
                position = later_reads.index(out)
                if later in AS_INTEGER:
                    use = 'integer window operand'
                elif later in KEYED and position == KEYED[later]:
                    use = f'{later.split("(")[-1]} key'
                elif later in ('SetTableInteger', 'SetTableArray', 'SetTableHref') and position == len(later_reads) - 1:
                    use = f'{later} stored value'
                else:
                    use = f'{later} operand {position}'
                break
            if later_out == out:
                use = 'overwritten unread'
                break
        uses[use] += max(samples, 1)
    total = sum(uses.values())
    print(f"integer windows' results, by their first reader, weighted by the window's samples ({total}):")
    for use, n in uses.most_common():
        print(f"  {n:6} {100 * n / total:5.1f}%  {use}")
    print(f"value stack stores: {stores['value stack store']} of {stores['all']} JIT samples")


if __name__ == '__main__':
    main()
