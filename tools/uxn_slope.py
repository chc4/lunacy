#!/usr/bin/env python3
"""Hardware counters per iteration of a uxn_* ROM's loop, from `just
perf-stat-uxn-slope-events` runs: each implementation's counts on the long ROM
and the short one, whose loops differ by `--iterations`, and the difference over
those, which leaves out starting the process, building the machine and compiling.
With more than one run's directory, each event's per-iteration count in each,
and the change from the first.

    tools/uxn_slope.py --iterations N DIR [DIR...]

Each DIR holds `<implementation>.long.csv` and `<implementation>.short.csv`, as
`perf stat -x, -o` writes them. A count perf multiplexed (counted for less than
all the run) is scaled by perf, and shown with how much of the run it counted.
"""
import argparse
import collections
from pathlib import Path


def counts(csv):
    """Each event's count, and the share of the run perf counted it for."""
    out = {}
    for line in Path(csv).read_text().splitlines():
        fields = line.split(',')
        if len(fields) < 5 or line.startswith('#'):
            continue
        value, event, share = fields[0], fields[2], fields[4]
        try:
            out[event] = (float(value), float(share or 100))
        except ValueError:
            out[event] = (None, 0.0)
    return out


def slopes(directory, iterations):
    """Implementation -> event -> (per-iteration count, least share counted)."""
    out = collections.defaultdict(dict)
    for long in sorted(Path(directory).glob('*.long.csv')):
        name = long.name[:-len('.long.csv')]
        short = long.with_name(f'{name}.short.csv')
        lc, sc = counts(long), counts(short)
        for event, (lv, ls) in lc.items():
            sv, ss = sc.get(event, (None, 0.0))
            out[name][event] = (None if lv is None or sv is None else (lv - sv) / iterations, min(ls, ss))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--iterations', type=int, required=True)
    ap.add_argument('dirs', nargs='+')
    args = ap.parse_args()
    runs = [(Path(d).name, slopes(d, args.iterations)) for d in args.dirs]
    names = sorted({name for _, run in runs for name in run})
    for name in names:
        print(f'{name.replace("_", " ")}: per iteration')
        events = list(dict.fromkeys(event for _, run in runs for event in run.get(name, {})))
        header = f'  {"event":32}' + ''.join(f'{label:>18}' for label, _ in runs)
        if len(runs) > 1:
            header += f'{"change":>10}'
        print(header)
        for event in events:
            cells, values = [], []
            for _, run in runs:
                value, share = run.get(name, {}).get(event, (None, 0.0))
                values.append(value)
                text = 'n/a' if value is None else f'{value:,.2f}'
                if value is not None and share < 99.5:
                    text += f' ({share:.0f}%)'
                cells.append(f'{text:>18}')
            row = f'  {event:32}' + ''.join(cells)
            if len(runs) > 1 and values[0] and values[-1] is not None:
                row += f'{100 * (values[-1] - values[0]) / values[0]:>+9.1f}%'
            print(row)
        cycles = [run.get(name, {}).get('cycles', (None, 0))[0] for _, run in runs]
        instructions = [run.get(name, {}).get('instructions', (None, 0))[0] for _, run in runs]
        if all(cycles) and all(instructions):
            print(f'  {"IPC":32}' + ''.join(f'{i / c:>18.2f}' for i, c in zip(instructions, cycles)))
        print()


if __name__ == '__main__':
    main()
