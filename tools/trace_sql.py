#!/usr/bin/env python3
"""Run SQL against a trace the `tracing` feature writes (`just trace`,
working/lunacy.fxt) in Perfetto's trace processor, and print the rows.

Events are slices; an event's arguments are `EXTRACT_ARG(arg_set_id, 'name')`.
The specializer's are also views, one column per argument:

  spec_version(ts, line, pc, outcome, block, versions, context, joined, shapes_dropped)
      each `Specializer::version`: the function's line, the pc, how the block
      was chosen (exact, fragile, new, accepting, joined, joined-new), the
      block, the versions at the pc after it, the context requested, the join
      (if one was made) and how many of the context's shapes it lost.
  spec_block(ts, block, line, pc, context)
      each version compiled.
  block_summary(block, line, pc, residuals, context, hotness, jitted)
      every block at the end of the run (line 0 for one no version names).

    tools/trace_sql.py [--trace working/lunacy.fxt] QUERY
(in the devshell, whose `trace_processor_shell` it runs; `just trace-sql`)
"""
import argparse
import shutil
from perfetto.trace_processor import TraceProcessor, TraceProcessorConfig

VIEWS = {
    'spec_version': ['line', 'pc', 'outcome', 'block', 'versions', 'context', 'joined', 'shapes_dropped'],
    'spec_block': ['block', 'line', 'pc', 'context'],
    'block_summary': ['block', 'line', 'pc', 'residuals', 'context', 'hotness', 'jitted'],
}
EVENTS = {'spec_version': 'version', 'spec_block': 'block', 'block_summary': 'block_summary'}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('query')
    ap.add_argument('--trace', default='working/lunacy.fxt')
    args = ap.parse_args()

    tp = TraceProcessor(trace=args.trace, config=TraceProcessorConfig(bin_path=shutil.which('trace_processor_shell')))
    for view, columns in VIEWS.items():
        extracted = ', '.join(f"EXTRACT_ARG(arg_set_id, '{c}') AS {c}" for c in columns)
        tp.query(f"CREATE PERFETTO VIEW {view} AS SELECT ts, {extracted} FROM slice "
                 f"WHERE category = 'spec' AND name = '{EVENTS[view]}'")
    result = tp.query(args.query)
    rows = [row for row in result]
    if not rows:
        print('(no rows)')
        return
    columns = [c for c in vars(rows[0])]
    table = [columns] + [[str(getattr(r, c)) for c in columns] for r in rows]
    widths = [max(len(row[i]) for row in table) for i in range(len(columns))]
    for row in table:
        print('  '.join(cell.ljust(w) for cell, w in zip(row, widths)).rstrip())


if __name__ == '__main__':
    main()
