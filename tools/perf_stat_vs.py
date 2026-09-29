#!/usr/bin/env python3
"""Instructions, branches and cycles (`perf stat`) of two builds of lunacy on
each run, `benchmark:times`, compiled by `just _luac`: its build A's counts, B's,
and B's change against A. Instructions and branches are the work done, which
code layout doesn't change, so they tell a change in work from one in layout,
which moves cycles only.

    perf_stat_vs.py --cpu CPU --runs N BENCH_A BENCH_B run...
"""
import argparse
import subprocess
import sys

EVENTS = ['instructions', 'branches', 'cycles']


def counts(binary, benchmark, times, cpu, runs):
    """The mean of each event over `runs` runs, pinned to `cpu`."""
    out = subprocess.run(['taskset', '-c', cpu, 'perf', 'stat', '-x,', '-r', str(runs), '-e', ','.join(EVENTS),
                          binary, f'working/{benchmark}.bin', times],
                         capture_output=True, text=True, check=True).stderr
    found = {}
    for line in out.splitlines():
        fields = line.split(',')
        if len(fields) > 2 and fields[2] in EVENTS:
            found[fields[2]] = float(fields[0])
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--cpu', default='2')
    parser.add_argument('--runs', type=int, default=3)
    parser.add_argument('a')
    parser.add_argument('b')
    parser.add_argument('runs_', nargs='+', metavar='run')
    args = parser.parse_args()
    print('| run | ' + ' | '.join(f'{e} A | B | Δ' for e in EVENTS) + ' |')
    print('|---|' + '---|---|---|' * len(EVENTS))
    for run in args.runs_:
        benchmark, times = run.split(':')
        subprocess.run(['just', '_luac', benchmark], check=True, capture_output=True)
        a = counts(args.a, benchmark, times, args.cpu, args.runs)
        b = counts(args.b, benchmark, times, args.cpu, args.runs)
        cells = [f'{a[e] / 1e6:.0f}M | {b[e] / 1e6:.0f}M | {100 * (b[e] / a[e] - 1):+.1f}%' for e in EVENTS]
        print(f'| {run} | ' + ' | '.join(cells) + ' |', flush=True)


if __name__ == '__main__':
    sys.exit(main())
