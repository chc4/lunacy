#!/usr/bin/env python3
"""The call continuations at the end of a run (`block_summary`) that guard on
a return id no return in a version still returns with: dead, as no callee can
return to them. Blocks no version names (line 0) are left out, both as
continuations and as returns, and so are the returns of versions the trimming
found unreachable; a guard on the unknown return id matches any return, and is
never dead.

    dead_continuations.py [working/lunacy.fxt] [--line LINE]

Prints, per function, how many continuations are live and dead, with the
dead ones' blocks, pcs, ids, and whether each has JIT code.
"""
import argparse
import shutil
from perfetto.trace_processor import TraceProcessor, TraceProcessorConfig

# Note [Call continuations] in `specialize`: the id with every bit below the
# effects set.
EFFECTS_SHIFT = 20
UNKNOWN_RETURN = (1 << EFFECTS_SHIFT) - 1


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('trace', nargs='?', default='working/lunacy.fxt')
    ap.add_argument('--line', type=int, help='only the continuations in the function at this line')
    args = ap.parse_args()
    tp = TraceProcessor(trace=args.trace, config=TraceProcessorConfig(bin_path=shutil.which('trace_processor_shell')))
    rows = list(tp.query(
        "SELECT EXTRACT_ARG(arg_set_id, 'block') AS block, EXTRACT_ARG(arg_set_id, 'line') AS line, "
        "EXTRACT_ARG(arg_set_id, 'pc') AS pc, EXTRACT_ARG(arg_set_id, 'jitted') AS jitted, "
        "EXTRACT_ARG(arg_set_id, 'returns') AS returns, EXTRACT_ARG(arg_set_id, 'returned_from') AS returned_from, "
        "EXTRACT_ARG(arg_set_id, 'unreachable') AS unreachable "
        "FROM slice WHERE category = 'spec' AND name = 'block_summary' AND EXTRACT_ARG(arg_set_id, 'line') != 0"))
    ids = lambda field: [int(id) for id in (field or '').split(',') if id]
    returned = {id for r in rows if not r.unreachable for id in ids(r.returns)}
    by_line = {}
    for r in rows:
        if args.line is not None and r.line != args.line:
            continue
        for id in ids(r.returned_from):
            live, dead = by_line.setdefault(r.line, ([], []))
            (live if id == UNKNOWN_RETURN or id in returned else dead).append((r.block, r.pc, id, r.jitted, r.unreachable))
    for line, (live, dead) in sorted(by_line.items()):
        print(f'line {line}: {len(live)} live, {len(dead)} dead continuations')
        for block, pc, id, jitted, unreachable in sorted(dead):
            print(f'  dead: block {block} pc {pc} returns from {id}{" (JIT code)" if jitted else ""}{" (unreachable)" if unreachable else ""}')


if __name__ == '__main__':
    main()
