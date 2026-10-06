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
  alloc_step(trace, step, line, block, pc, off)
      each step of each trace the window planner planned: the block it is in
      and, for a residual, its offset (a block's start's is 2^64-1).
  alloc_start(trace, step, rise, arrives, worth, entry)
      each block start planned: whether its edge rises into a loop, the
      window the trace arrives with and each value's worth there (its next
      use's distance, `exit n` if only a side exit's, `-` for none), and the
      entry window chosen.
  alloc_op(trace, step, name, before, worth, skip, emits, after)
      each window op planned: the window before it and its values' worth, its
      SKIP, what it emits (stores, loads, moves), and the window after.
  contractible(ts, line, pc, duplicates, origins, context)
      each version about to be compiled at `pc` for `context` while versions
      (`duplicates`) differ from it only in facts no code relied on: the
      blocks introducing those facts are queued for contraction.
  contract(ts, line, origins, how, offsets, forgotten)
      each contraction: the blocks rebuilt from where they introduced the
      facts (at those residual offsets), how (`drop`, without the facts,
      `integer`, with their constants loaded as integers, or `double`, an
      integer op computing in doubles), and the versions forgotten.
  unreachable(ts, line, reached, dropped)
      after a round of contractions: how many blocks the code they replaced
      reached, and those of them no longer reachable, whose versions were
      forgotten.
  contract_deferred(ts, line, origins, at)
      a queued contraction waiting while the interpreter (in block `at`) or a
      frame returning still runs code rebuilding replaces.
  contract_refused(ts, line, origins, how, reason)
      a queued contraction dropped: a fact `used` since, an origin `compiled`,
      or every origin `rebuilt` already.

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
    'alloc_step': ['trace', 'step', 'line', 'block', 'pc', 'off'],
    'alloc_start': ['trace', 'step', 'rise', 'arrives', 'worth', 'entry'],
    'alloc_op': ['trace', 'step', 'name', 'before', 'worth', 'skip', 'emits', 'after'],
    'contractible': ['line', 'pc', 'duplicates', 'origins', 'context'],
    'contract': ['line', 'origins', 'how', 'offsets', 'forgotten'],
    'contract_deferred': ['line', 'origins', 'at'],
    'contract_refused': ['line', 'origins', 'how', 'reason'],
    'unreachable': ['line', 'reached', 'dropped'],
}
EVENTS = {'spec_version': ('spec', 'version'), 'spec_block': ('spec', 'block'), 'block_summary': ('spec', 'block_summary'),
          'alloc_step': ('alloc', 'step'), 'alloc_start': ('alloc', 'start'), 'alloc_op': ('alloc', 'op'),
          'contractible': ('spec', 'contractible'), 'contract': ('spec', 'contract'),
          'contract_deferred': ('spec', 'contract_deferred'), 'contract_refused': ('spec', 'contract_refused'),
          'unreachable': ('spec', 'unreachable')}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('query')
    ap.add_argument('--trace', default='working/lunacy.fxt')
    args = ap.parse_args()

    tp = TraceProcessor(trace=args.trace, config=TraceProcessorConfig(bin_path=shutil.which('trace_processor_shell')))
    for view, columns in VIEWS.items():
        extracted = ', '.join(f"EXTRACT_ARG(arg_set_id, '{c}') AS {c}" for c in columns)
        category, name = EVENTS[view]
        tp.query(f"CREATE PERFETTO VIEW {view} AS SELECT ts, {extracted} FROM slice "
                 f"WHERE category = '{category}' AND name = '{name}'")
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
