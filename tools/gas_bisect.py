#!/usr/bin/env python3
"""The least gas with which a program's run by lunacy goes wrong: its output differs from
Lua 5.1's, or it crashes. Gas (feature `gas`) counts the residuals JIT code runs and exits
to the interpreter once it is spent (`LUNACY_GAS`), so a run with less gas runs less of the
JIT's code; the least gas that goes wrong ends just past the JIT code that miscompiles.

    tools/gas_bisect.py BYTECODE SOURCE LUNACY [--max N] [--signature TEXT]

BYTECODE is SOURCE compiled by luac5.1, LUNACY a `lunacy` binary built with `gas`. A run
stopped by gas at a point it can't stop at cleanly can fail otherwise: `--signature` counts
only the failures whose stderr has it (a panic's location). Prints
each run tried, then the least gas going wrong: its output, and the residuals it ran as its
gas ran low (lunacy's `low gas` report).
"""
import argparse
import os
import subprocess


def output(cmd, env=None):
    r = subprocess.run(cmd, capture_output=True, text=True, env=env, timeout=600)
    # lunacy's reports of its run, and of where gas ran out, aren't the program's output.
    report = ('counters after run', 'out of gas', 'low gas')
    lines = [l for l in r.stdout.splitlines() if not l.startswith(report)]
    low = [l for l in r.stdout.splitlines() if l.startswith(('out of gas', 'low gas'))]
    return r.returncode, lines, r.stderr, low


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('bytecode')
    ap.add_argument('source')
    ap.add_argument('lunacy')
    ap.add_argument('--max', type=int, default=1 << 40)
    ap.add_argument('--signature', default='', help='only a run whose stderr has this goes wrong: one failure of several')
    args = ap.parse_args()
    _, expected, _, _ = output(['lua5.1', args.source])

    def wrong(gas):
        code, lines, err, low = output([args.lunacy, args.bytecode], dict(os.environ, LUNACY_GAS=str(gas), RUST_BACKTRACE='1'))
        bad = (code != 0 or lines != expected) and args.signature in err
        errs = err.strip().splitlines()
        at = next((i for i, l in enumerate(errs) if 'panicked at' in l), None)
        why = ' '.join(errs[at:at + 2]) if bad and at is not None else ''
        print(f'gas {gas}: {"wrong" if bad else "right"} (exit {code}) {why[:200]}')
        return bad, lines, err, low

    bad, lines, _, _ = wrong(0)
    if bad:
        print('wrong with no JIT code run: not a JIT miscompile')
        print('expected:', expected)
        print('output:  ', lines)
        return
    if not wrong(args.max)[0]:
        print(f'right with {args.max} gas')
        return
    lo, hi = 0, args.max
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if wrong(mid)[0]:
            hi = mid
        else:
            lo = mid
    print(f'\nleast gas going wrong: {hi}')
    _, lines, err, low = wrong(hi)
    print('expected:', expected)
    print('output:  ', lines)
    print('stderr:', '\n'.join(l for l in err.strip().splitlines() if 'panicked' in l or 'lunacy::' in l or not l.startswith(' '))[:3000])
    print('where the gas ran low, last:')
    print('\n'.join(low[-12:]))


main()
