#!/usr/bin/env python3
"""One function's compiled blocks, in pc order, from three runs of the same
benchmark and features: the trace's blocks of the function at `line` (`just
trace`, with their residuals), their machine code (`just jit-disasm`, the
instructions each residual compiles to) and their samples (`just flamegraph`).
Block ids are the runs' own: a block whose residuals differ between the trace
and the disassembly is marked `mismatch`, as its id named another block in one
of the runs.

    tools/function_blocks.py LINE [--trace working/lunacy.fxt]
        [--disasm working/jit_disasm.txt] [--perf working/perf.data] [--hot 0.0]
"""
import argparse
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from trace_sql import connect
from jit_block_profile import blocks as disasm_blocks, samples as profile_samples


def names(residuals):
    """Each residual's name, as both the trace and the disassembly print it."""
    return [re.match(r'[a-z_]+', r).group(0) for r in residuals if re.match(r'[a-z_]+', r)]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('line', type=int)
    ap.add_argument('--trace', default='working/lunacy.fxt')
    ap.add_argument('--disasm', default='working/jit_disasm.txt')
    ap.add_argument('--perf', default='working/perf.data')
    ap.add_argument('--hot', type=float, default=0.0, help='only blocks with at least this share of samples')
    args = ap.parse_args()
    rows = list(connect(args.trace).query(
        f"select block, pc, code from block_summary where line = {args.line} and compiled = 1 order by pc, block"))
    code = disasm_blocks(args.disasm)
    shares = profile_samples(args.perf)
    total_share, total_insns = 0.0, 0
    for r in rows:
        share = shares.get(r.block, 0.0)
        if share < args.hot:
            continue
        traced = [c.strip() for c in (r.code or '').split(';') if c.strip()]
        compiled = code.get(r.block, {}).get('residuals', [])
        insns = sum(len(i) for _, i in compiled)
        match = names(traced) == names([res for res, _ in compiled if res != '(block entry)'])
        total_share += share
        total_insns += insns
        detail = '; '.join(f'{res} [{len(i)}]' for res, i in compiled) if compiled else '; '.join(traced)
        print(f'pc {r.pc:3} block {r.block:5} {share:5.2f}% {insns:4} insns{"" if match or not compiled else " mismatch"}: {detail}')
    print(f'total {total_share:.2f}% of samples, {total_insns} instructions')


if __name__ == '__main__':
    main()
