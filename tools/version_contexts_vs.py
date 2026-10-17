#!/usr/bin/env python3
"""The contexts of the versions a function compiles at a point in two traces
of the same program (as `just trace-golden-rev` and `just trace-golden` make),
addresses blanked: those only one trace has, to see which knowledge splits
versions one revision makes and the other doesn't.

    tools/version_contexts_vs.py LINE PC BASE.fxt HEAD.fxt
"""
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from trace_sql import connect


def contexts(trace, line, pc):
    rows = connect(trace).query(f"select context from spec_version where line = {line} and pc = {pc} and outcome = 'new'")
    return {re.sub(r'0x[0-9a-f]+', '0x_', r.context) for r in rows}


def main():
    line, pc, base, head = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
    a, b = contexts(base, line, pc), contexts(head, line, pc)
    print(f'{len(a)} contexts in {base}, {len(b)} in {head}, {len(a & b)} in both')
    for name, only in (('only in ' + base, a - b), ('only in ' + head, b - a)):
        print(f'\n{name}:')
        for c in sorted(only):
            print('  ' + c)


if __name__ == '__main__':
    main()
