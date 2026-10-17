"""Runs of integer windows in a sampled disassembly (`just jit-profile`'s
working/jit_samples.txt): each run of integer windows the code falls through,
the `branch`es between them skipped, by its windows and the residual after it,
weighted by the run's samples. Which chains a peephole fusing them would see,
and how often.

    tools/window_chains.py working/jit_samples.txt [--top N]
"""
import argparse
import collections
import re

INTEGER = {'IntegerRK', 'IntegerRR', 'IntegerKR', 'MaskRK', 'FloorShiftK'}
RESIDUAL = re.compile(r"\s*; \d+ (.*)$")
INSN = re.compile(r"\s*(\d*)\s+[0-9a-f]{8,}\s")


def name(text):
    """A residual's name: a window's own, a dynamic guard's test, else its first word."""
    if m := re.match(r"window\((\w+)", text):
        return m.group(1)
    if m := re.match(r"guard_dynamic\((\w+)", text):
        return f"guard_dynamic:{m.group(1)}"
    return re.match(r"\S*?(?=\(|$)", text).group(0) or text.split()[0]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('samples')
    ap.add_argument('--top', type=int, default=14)
    args = ap.parse_args()
    stream = []
    for line in open(args.samples):
        if m := RESIDUAL.match(line):
            stream.append([name(m.group(1)), 0])
        elif (m := INSN.match(line)) and stream:
            stream[-1][1] += int(m.group(1) or 0)
    chains, lengths = collections.Counter(), collections.Counter()
    i = 0
    while i < len(stream):
        if stream[i][0] not in INTEGER:
            i += 1
            continue
        j = i
        while j < len(stream) and stream[j][0] in INTEGER | {'branch'}:
            j += 1
        ops = [n for n, _ in stream[i:j] if n != 'branch']
        after = stream[j][0] if j < len(stream) else 'end'
        samples = sum(s for _, s in stream[i:j])
        chains[' ; '.join(ops) + '  ->  ' + after] += samples
        lengths[len(ops)] += samples
        i = j
    total = sum(chains.values())
    print(f"runs of integer windows, by samples ({total}), and the residual after each:")
    for chain, n in chains.most_common(args.top):
        print(f"  {n:6} {100 * n / total:5.1f}%  {chain}")
    print("by windows in the run: " + ", ".join(f"{k}: {100 * v / total:.0f}%" for k, v in sorted(lengths.items())))


if __name__ == '__main__':
    main()
