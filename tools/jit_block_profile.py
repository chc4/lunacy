#!/usr/bin/env python3
"""Join a perf profile's samples per JIT block (`just flamegraph`, the `perf`
feature's `jit_block_<id>` symbols) with the JIT's disassembly of those blocks
(`just jit-disasm`, working/jit_disasm.txt) of the same benchmark and features:
the hottest blocks, each with its share of samples, its instructions and its
residuals; and the samples by residual kind, each block's share split over its
residuals by how many instructions each one's code is.

Both runs must compile the same blocks: the same benchmark, times and
features but for `perf`/`jit_disasm`.

    tools/jit_block_profile.py [--perf working/perf.data] [--disasm working/jit_disasm.txt] [--top 25]
"""
import argparse
import collections
import re
import subprocess

BLOCK = re.compile(r'^  ; block (\d+) \(pc (\d+)')
RESIDUAL = re.compile(r'^  ;\s+(\d+) (.*)$')
INSN = re.compile(r'^  [0-9a-f]{12} \+[0-9a-f]+ +[0-9a-f]+ +(\S.*)$')
REGION = re.compile(r'^==== region entered at block \d+, function (:\d+)')


def blocks(path):
    """Each block's function, pc and residuals, each with its instructions."""
    out = {}
    block = None
    function = None
    for line in open(path):
        if m := REGION.match(line):
            function = m.group(1)
            block = None
        elif line.startswith('==== '):
            block = None
        elif m := BLOCK.match(line):
            block = out.setdefault(int(m.group(1)), {'function': function, 'pc': int(m.group(2)), 'residuals': []})
        elif block is not None and (m := RESIDUAL.match(line)):
            block['residuals'].append([m.group(2), []])
        elif block is not None and (m := INSN.match(line)):
            if not block['residuals']:
                block['residuals'].append(['(block entry)', []])
            block['residuals'][-1][1].append(m.group(1))
    return out


def samples(path):
    """Each JIT block's share of the profile's samples, in percent."""
    report = subprocess.run(['perf', 'report', '-i', path, '--no-children', '--sort', 'sym', '--stdio', '-g', 'none'],
                            capture_output=True, text=True).stdout
    out = {}
    for line in report.splitlines():
        if m := re.match(r'^\s+([0-9.]+)%.*jit_block_(\d+)\b', line):
            out[int(m.group(2))] = out.get(int(m.group(2)), 0) + float(m.group(1))
    return out


def kind(residual):
    """A residual's kind: its name and, for a window op or a dynamic guard, the op's."""
    m = re.match(r'(\w+)(?:\((\w+))?', residual)
    if not m:
        return residual
    return f'{m.group(1)}({m.group(2)})' if m.group(1) in ('window', 'guard_dynamic') and m.group(2) else m.group(1)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--perf', default='working/perf.data')
    ap.add_argument('--disasm', default='working/jit_disasm.txt')
    ap.add_argument('--top', type=int, default=25)
    args = ap.parse_args()
    code = blocks(args.disasm)
    shares = samples(args.perf)
    total = sum(shares.values())
    print(f'{total:.1f}% of samples in JIT blocks; {sum(1 for b in shares if b not in code)} sampled blocks not in the disassembly')
    by_kind = collections.Counter()
    for block, share in shares.items():
        residuals = code.get(block, {}).get('residuals', [])
        insns = sum(len(i) for _, i in residuals)
        for residual, i in residuals:
            if insns:
                by_kind[kind(residual)] += share * len(i) / insns
    print('\nsamples by residual kind (block shares split by instruction count):')
    for k, share in by_kind.most_common(20):
        print(f'  {share:5.1f}%  {k}')
    print(f'\nhottest {args.top} blocks:')
    for block, share in sorted(shares.items(), key=lambda kv: -kv[1])[:args.top]:
        b = code.get(block)
        if not b:
            print(f'{share:5.2f}%  block {block}: not in the disassembly')
            continue
        insns = sum(len(i) for _, i in b['residuals'])
        print(f'{share:5.2f}%  block {block} {b["function"]} pc {b["pc"]}, {insns} instructions: ' +
              '; '.join(f'{r} [{len(i)}]' for r, i in b['residuals']))


if __name__ == '__main__':
    main()
