#!/usr/bin/env python3
"""How many cold-path site records a run's JIT code has, and how many are the
same but for their fall-through address: from the `site record of <op>:
captures [...]` notes in its annotated disassembly (`just jit-disasm`). Counts
them per region (the pool a record is laid in) and over the whole run, and
lists the capture tuples most repeated. See Note [Cold stencils].

    site_records.py [working/jit_disasm.txt] [--top N]
"""
import argparse
import re
from collections import Counter

REGION = re.compile(r'^==== (.*) @ 0x[0-9a-f]+, \d+ bytes$')
RECORD = re.compile(r'^\s*; site record of (\w+): captures (\[.*\])$')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('disasm', nargs='?', default='working/jit_disasm.txt')
    ap.add_argument('--top', type=int, default=10)
    args = ap.parse_args()

    regions = []
    for line in open(args.disasm):
        if REGION.match(line):
            regions.append(Counter())
        elif (m := RECORD.match(line)) and regions:
            regions[-1][(m.group(1), m.group(2))] += 1

    total = sum(sum(r.values()) for r in regions)
    distinct_per_region = sum(len(r) for r in regions)
    overall = Counter()
    for r in regions:
        overall.update(r)
    print(f'{total} site records in {sum(1 for r in regions if r)} regions')
    print(f'{distinct_per_region} distinct within their region, {len(overall)} distinct over the run')
    print(f'\nmost repeated (op, captures), over the run:')
    for (op, captures), n in overall.most_common(args.top):
        print(f'  {n:>5}  {op} {captures}')


if __name__ == '__main__':
    main()
