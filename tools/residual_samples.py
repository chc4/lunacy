"""Compare two `just jit-profile` runs of one benchmark residual by residual.

Each argument is the sampled disassembly `jit-profile` writes (working/jit_samples.txt):
every instruction with its sample count, under the note of the block it is in and of the
residual that emitted it. Block ids differ between builds, so samples are summed by the
block's pc and the residual's text (its index in the block dropped): the same residual at
the same pc in every version and copy of it is one row. Prints the rows with the most
samples in either run, each run's count, and the change.
"""
import argparse, collections, re

BLOCK = re.compile(r"\s*; block (\d+) \(pc (\d+)")
RESIDUAL = re.compile(r"\s*; (\d+) (.*)")
SAMPLED = re.compile(r"\s*(\d+)\s+[0-9a-f]{8,}\s")


def residual_samples(path):
    """(pc, residual) -> samples, and pc -> the residuals of its sampled blocks."""
    counts = collections.Counter()
    pc, residual = None, None
    for line in open(path):
        if m := BLOCK.match(line):
            pc, residual = int(m.group(2)), '(block entry)'
        elif m := RESIDUAL.match(line):
            residual = m.group(2)
        elif (m := SAMPLED.match(line)) and pc is not None:
            counts[(pc, residual)] += int(m.group(1))
    return counts


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('base')
    parser.add_argument('head')
    parser.add_argument('--top', type=int, default=40)
    args = parser.parse_args()
    base, head = residual_samples(args.base), residual_samples(args.head)
    keys = sorted(set(base) | set(head), key=lambda k: -max(base[k], head[k]))[:args.top]
    print(f"{'pc':>4}  {'residual':48} {'base':>7} {'head':>7} {'change':>7}")
    for pc, residual in sorted(keys):
        b, h = base[(pc, residual)], head[(pc, residual)]
        print(f"{pc:>4}  {residual[:48]:48} {b:>7} {h:>7} {h - b:>+7}")
    print(f"{'':>4}  {'all JIT samples':48} {sum(base.values()):>7} {sum(head.values()):>7} {sum(head.values()) - sum(base.values()):>+7}")


if __name__ == '__main__':
    main()
