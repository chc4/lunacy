#!/usr/bin/env python3
"""Steady-state time per iteration of a benchmark from two `hyperfine-uxn-promote`
runs of it, at `low` and `high` times: per command, the median at each, the
time per iteration past the first, (high - low) / (high - low times), and the
warm-up, the low median less that many iterations.

    tools/steady_state.py uxn_fib [--low 1] [--high 4]
"""
import argparse
import json
import statistics


def medians(benchmark, times):
    data = json.load(open(f'working/hyperfine-promote-{benchmark}-{times}.json'))
    return {r['command']: (statistics.median(r['times']) * 1000, set(r.get('exit_codes', [0]))) for r in data['results']}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('benchmark')
    ap.add_argument('--low', type=int, default=1)
    ap.add_argument('--high', type=int, default=4)
    args = ap.parse_args()
    low, high = medians(args.benchmark, args.low), medians(args.benchmark, args.high)
    for command, (lo, lcodes) in low.items():
        if command not in high:
            print(f'{command:22} n={args.low} {lo:9.1f} ms (one run of the ROM)')
            continue
        hi, hcodes = high[command]
        steady = (hi - lo) / (args.high - args.low)
        failed = '' if lcodes | hcodes == {0} else f'  exit {sorted(lcodes | hcodes)}'
        print(f'{command:22} n={args.low} {lo:9.1f}  n={args.high} {hi:9.1f}  steady/iter {steady:9.1f}  warm-up {lo - steady * args.low:8.1f} ms{failed}')


if __name__ == '__main__':
    main()
