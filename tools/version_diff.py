#!/usr/bin/env python3
"""The first point two traces' specializers decide differently: each trace's
`spec_version` and `contract` events in order (`tools/trace_sql.py`), a version
as its line, pc, outcome and context, a contraction as its line, how and
offsets (block numbers and the addresses in a context differ between runs, so
they are left out), compared until they differ, with the events around there
from each.

With `--live`, instead the versions each run has at its end (`block_summary`),
per function and pc: how many each has, and the contexts only one of them has.
`--lines OLD:NEW,...` compares the function at line OLD of the old trace as
the one at line NEW of the new, for a function the two runs load from
different places.

    version_diff.py OLD.fxt NEW.fxt [--context N] [--live [--lines OLD:NEW,...]]
"""
import argparse
import re
import shutil
from perfetto.trace_processor import TraceProcessor, TraceProcessorConfig


def events(path):
    tp = TraceProcessor(trace=path, config=TraceProcessorConfig(bin_path=shutil.which('trace_processor_shell')))
    rows = tp.query("SELECT ts, EXTRACT_ARG(arg_set_id, 'line') AS line, EXTRACT_ARG(arg_set_id, 'pc') AS pc, "
                    "EXTRACT_ARG(arg_set_id, 'outcome') AS outcome, EXTRACT_ARG(arg_set_id, 'block') AS block, "
                    "EXTRACT_ARG(arg_set_id, 'context') AS context FROM slice "
                    "WHERE category = 'spec' AND name = 'version' ORDER BY ts")
    versions = [(r.ts, r.line, r.pc, r.outcome, r.block, r.context) for r in rows]
    rows = tp.query("SELECT ts, EXTRACT_ARG(arg_set_id, 'line') AS line, EXTRACT_ARG(arg_set_id, 'how') AS how, "
                    "EXTRACT_ARG(arg_set_id, 'offsets') AS offsets, EXTRACT_ARG(arg_set_id, 'origins') AS origins FROM slice "
                    "WHERE category = 'spec' AND name = 'contract' ORDER BY ts")
    contracts = [(r.ts, r.line, f'@{r.offsets}', 'contract', r.origins, r.how) for r in rows]
    return sorted(versions + contracts, key=lambda e: e[0])


def live(path, lines=None):
    tp = TraceProcessor(trace=path, config=TraceProcessorConfig(bin_path=shutil.which('trace_processor_shell')))
    rows = tp.query("SELECT EXTRACT_ARG(arg_set_id, 'line') AS line, EXTRACT_ARG(arg_set_id, 'pc') AS pc, "
                    "EXTRACT_ARG(arg_set_id, 'context') AS context FROM slice "
                    "WHERE category = 'spec' AND name = 'block_summary' AND EXTRACT_ARG(arg_set_id, 'line') != 0")
    versions = {}
    for r in rows:
        line = lines.get(r.line, r.line) if lines else r.line
        versions.setdefault((line, r.pc), []).append(re.sub(r'0x[0-9a-f]+', '0x_', r.context))
    return versions


def compare_live(old, new):
    for at in sorted(set(old) | set(new), key=lambda at: (str(at[0]), at[1])):
        o, n = sorted(old.get(at, [])), sorted(new.get(at, []))
        if o == n:
            continue
        print(f'line {at[0]} pc {at[1]}: {len(o)} and {len(n)}')
        for context in o:
            if context not in n:
                print(f'  only old: {context}')
        for context in n:
            if context not in o:
                print(f'  only new: {context}')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('old')
    ap.add_argument('new')
    ap.add_argument('--context', type=int, default=6)
    ap.add_argument('--live', action='store_true')
    ap.add_argument('--lines', help='OLD:NEW,... line pairs naming one function in each trace')
    args = ap.parse_args()
    if args.live:
        pairs = [pair.split(':') for pair in args.lines.split(',')] if args.lines else []
        old_lines = {int(o): f'{o}:{n}' for o, n in pairs}
        new_lines = {int(n): f'{o}:{n}' for o, n in pairs}
        compare_live(live(args.old, old_lines), live(args.new, new_lines))
        return
    old, new = events(args.old), events(args.new)
    key = lambda e: e[1:4] + (re.sub(r'0x[0-9a-f]+', '0x_', e[5]),)
    at = next((i for i, (o, n) in enumerate(zip(old, new)) if key(o) != key(n)), None)
    if at is None:
        print(f'the same {min(len(old), len(new))} decisions; {len(old)} and {len(new)} in all')
        return
    print(f'{at} decisions the same, then:')
    for name, trace in (('old', old), ('new', new)):
        print(f'== {name}')
        for i in range(max(0, at - args.context), min(len(trace), at + args.context)):
            ts, line, pc, outcome, block, context = trace[i]
            print(f"{'>' if i == at else ' '} {ts:>10} line {line:<4} pc {pc:<4} {outcome:<10} block {block:<5} {context}")


if __name__ == '__main__':
    main()
