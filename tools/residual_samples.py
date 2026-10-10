"""Compare two `just jit-profile` runs of one benchmark residual by residual.

Each argument is the sampled disassembly `jit-profile` writes (working/jit_samples.txt):
every instruction with its sample count, under the note of the region it is in, of its block
and of the residual that emitted it. Block ids differ between builds, so samples are summed
by the block's function (as its note names it, `725-693` for 693's inlined into 725's, or for
a dump without, its region's), the block's pc (where the block starts, which may be some
instructions before the residual's) and the residual's text, its index in the block and the
blocks it names dropped: the same residual at the same pc in every version and copy of it is
one row. Code under any other note (a region's exits and epilogue) is its own row, as is code
under none. Prints the rows with the most samples in either run, each run's count, and the
change.
"""
import argparse, collections, re

REGION = re.compile(r"==== region entered at block \d+, function :(\d+)")
BLOCK = re.compile(r"\s*; block (\d+) \(pc (\d+)(?:, function ([\d?-]+))?")
RESIDUAL = re.compile(r"\s*; (\d+) (.*)")
# Any other note: code a region lays out around its blocks (an exit, an epilogue).
NOTE = re.compile(r"\s*; (.*)")
SAMPLED = re.compile(r"\s*(\d+)\s+[0-9a-f]{8,}\s")
TARGETS = re.compile(r"(jump|branch|select)\([\d, ]*\)")


def residual_samples(path):
    """(function, pc, residual) -> samples."""
    counts = collections.Counter()
    region, function, pc, residual = None, None, None, None
    for line in open(path):
        if m := REGION.match(line):
            region = m.group(1)
        elif m := BLOCK.match(line):
            function, pc, residual = m.group(3) or region, int(m.group(2)), '(block entry)'
        elif m := RESIDUAL.match(line):
            residual = TARGETS.sub(r"\1", m.group(2))
        elif (m := NOTE.match(line)) and not SAMPLED.match(line):
            residual = '(' + re.sub(r'\d+', 'N', m.group(1)) + ')'
        elif not line.strip():
            # A gap in the dump: what follows is another range, not this residual's.
            residual = '(unnoted)'
        elif (m := SAMPLED.match(line)) and pc is not None:
            counts[(function, pc, residual)] += int(m.group(1))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('base')
    parser.add_argument('head')
    parser.add_argument('--top', type=int, default=40)
    args = parser.parse_args()
    base, head = residual_samples(args.base), residual_samples(args.head)
    keys = sorted(set(base) | set(head), key=lambda k: -max(base[k], head[k]))[:args.top]
    print(f"{'function':>12} {'pc':>4}  {'residual':48} {'base':>7} {'head':>7} {'change':>7}")
    for key in sorted(keys, key=lambda k: (k[0] or '', k[1], k[2])):
        b, h = base[key], head[key]
        print(f"{key[0] or '?':>12} {key[1]:>4}  {key[2][:48]:48} {b:>7} {h:>7} {h - b:>+7}")
    print(f"{'':>12} {'':>4}  {'all JIT samples':48} {sum(base.values()):>7} {sum(head.values()):>7} {sum(head.values()) - sum(base.values()):>+7}")


if __name__ == '__main__':
    main()
