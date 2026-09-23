#!/usr/bin/env python3
"""List the runs of window residuals in `graph` feature dumps (func_N.dot).

Each block is printed with how many times the interpreter entered it (hottest
first), its residuals, and each run of `ExecWindow` residuals as the ops it
holds, operands in window order by stack slot, outputs marked `out`.
See docs/jit-register-cache.md; `just window-runs` produces the dumps.
"""
import argparse
import re
import sys

BLOCK = re.compile(r'(\d+)\[id=\d+,shape=record,label="(.*?)"\]\n')


def blocks(dot):
    """(block id, times entered, residual labels) for each of the dumped
    function's blocks: a dump lists every block, but only the function's own
    carry their context (`{ PC: ...`) before the residuals."""
    for m in BLOCK.finditer(dot):
        items = [item.strip() for item in m.group(2).split('|')]
        if not items[1].startswith('{ PC:'):
            continue
        head = items[0].split(' x')
        entered = int(head[1]) if len(head) > 1 else 0
        residuals = [r.rstrip(' }').replace('\\>', '>').replace('\\<', '<') for r in items[2:]]
        yield int(m.group(1)), entered, [r for r in residuals if r]


def describe(residuals):
    """The residuals, each run of window residuals collapsed into its ops."""
    run, out = [], []
    for r in residuals:
        if r.startswith('window('):
            name, *operands = r[len('window('):-1].split(', ')
            run.append('%s(%s)' % (name, ', '.join(operands)))
        else:
            if run:
                out.append('RUN[%d]: %s' % (len(run), '; '.join(run)))
                run = []
            out.append(r)
    if run:
        out.append('RUN[%d]: %s' % (len(run), '; '.join(run)))
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('dumps', nargs='+', help='func_N.dot files')
    parser.add_argument('--min', type=int, default=1, help='only blocks entered at least this often')
    args = parser.parse_args()
    for path in args.dumps:
        found = sorted((b for b in blocks(open(path).read()) if b[1] >= args.min), key=lambda b: -b[1])
        found = [(bid, entered, describe(residuals)) for bid, entered, residuals in found]
        found = [b for b in found if any(r.startswith('RUN[') for r in b[2])]
        if not found:
            continue
        print('==', path)
        for bid, entered, lines in found:
            print('block %d x%d' % (bid, entered))
            for line in lines:
                print('    ' + line)
    return 0


if __name__ == '__main__':
    sys.exit(main())
