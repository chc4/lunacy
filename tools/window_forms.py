#!/usr/bin/env python3
"""How often each kind of window op ran with its output boxed or unboxed, from
a run's `window_dump.txt` (`just window-dump`): per op (by its residual's
name), the executions of copies whose output the window then holds unboxed in
an XMM register (`x`) and boxed in a general register (`w`), most run first.
An op runs as often as the counted code it emits (its line's `#N`); its output
is the slot after `out`. See Note [Unboxed doubles] in `window_alloc`.

    window_forms.py [working/window_dump.txt] [--op PREFIX]
"""
import argparse
import re
from collections import defaultdict

RESIDUAL = re.compile(r'^\s+\d+ window\((\w+),.*\bout (\d+)\)$')
COUNTED = re.compile(r'#(\d+)$')
WINDOW = re.compile(r'^\s+window \{(.*)\}$')
COUNT = re.compile(r'^count #(\d+) (\d+)$')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('dump', nargs='?', default='working/window_dump.txt')
    ap.add_argument('--op', default='', help='only ops whose name starts with this')
    args = ap.parse_args()

    # (op, form) per counted site, then the counts.
    sites, counts = [], {}
    pending = None
    for line in open(args.dump):
        line = line.rstrip('\n')
        if m := COUNT.match(line):
            counts[int(m.group(1))] = int(m.group(2))
        elif m := RESIDUAL.match(line):
            pending = [m.group(1), m.group(2), None]
        elif pending and pending[2] is None and (m := COUNTED.search(line)):
            pending[2] = int(m.group(1))
        elif pending and (m := WINDOW.match(line)):
            op, slot, site = pending
            form = next((reg[0] for reg in m.group(1).split() if reg.split('=')[1].rstrip('*') == f'[{slot}]'), None)
            if site is not None and form is not None:
                sites.append((op, form, site))
            pending = None

    runs = defaultdict(lambda: {'x': 0, 'w': 0})
    for op, form, site in sites:
        if op.startswith(args.op):
            runs[op][form] += counts.get(site, 0)
    print(f"{'op':20} {'unboxed (x)':>14} {'boxed (w)':>14}")
    for op, n in sorted(runs.items(), key=lambda kv: -(kv[1]['x'] + kv[1]['w'])):
        print(f"{op:20} {n['x']:>14} {n['w']:>14}")


if __name__ == '__main__':
    main()
