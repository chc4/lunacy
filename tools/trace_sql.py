#!/usr/bin/env python3
"""Run SQL against a trace the `tracing` feature writes (`just trace`,
working/lunacy.fxt) in Perfetto's trace processor, and print the rows.

Events are slices; an event's arguments are `EXTRACT_ARG(arg_set_id, 'name')`.
The specializer's are also views, one column per argument:

  spec_version(ts, line, pc, outcome, block, versions, context, joined, shapes_dropped, origins)
      each `Specializer::version`: the function's line, the pc, how the block
      was chosen (exact, fragile, new, accepting, joined, joined-new), the
      block, the versions at the pc after it, the context requested, the join
      (if one was made), how many of the context's shapes it lost, and where
      each of its fragile facts was introduced (`fact <- block@offset,...`).
  spec_block(ts, block, line, pc, context)
      each version created, whatever became of it since: counting its rows
      counts versions ever made, not versions in the graph (`point_versions`).
  version_fate(ts, block, line, pc, fate, at)
      each version created (as `spec_block`), and what became of it: `live`,
      in the graph at the end; `forgotten` by a contraction, or `evicted` from
      its point, at `at`; or `unreachable` at the end, still in the version
      map: the trimming found it so and no lookup in the map found it since,
      but code already linked to it (a jump, JIT code's) may still run it.
      A block id is used again once its version is forgotten, so a version's
      fate is that of its id until the id's next version.
  point_versions(line, pc, created, live, unreachable, evicted, forgotten)
      per point, its versions by fate: `live` and `unreachable` are what the
      graph has there at the end. How often a version ran isn't in a trace:
      `just jit-profile` samples the JIT's, the interpreter tier's graph dump
      (`just window-runs`) counts every entry.
  block_summary(block, line, pc, residuals, code, context, hotness, jitted, returns, returned_from, unreachable)
      every block at the end of the run (line 0 for one no version names),
      with the return ids its returns return with, those its call
      continuations guard on (comma separated), and whether the trimming
      found it unreachable (forgotten once its point needs the room).
      `hotness` counts down from 64, one for each time the interpreter
      entered the block, to 0 when it tiers up: 64 is never entered there, 0
      is compiled, and JIT code's entries don't count.
  inline_refused(line, callee, call_block, reason)
      each call's continuation that didn't inline its callee: `compiled` (its
      call's block had JIT code by its first return), `relaid` (the call was
      laid out again), or `policy` (`inlines` says no: size, depth, loops).
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
  contractible(ts, line, pc, duplicates, origins, context, theirs)
      each version about to be compiled at `pc` for `context` while versions
      (`duplicates`) differ from it only in facts no code relied on, or in a
      constant's slot holding another type: the blocks introducing those
      facts are queued for contraction. `theirs` is each duplicate's context,
      after which of the two it was (`unused`, `retyped`).
  contract(ts, line, origins, how, offsets, forgotten)
      each contraction: the blocks rebuilt from where they introduced the
      facts (at those residual offsets), how (`drop`, without the facts,
      `double`, with their constants loaded as doubles, or an integer op
      computing in doubles), and the versions forgotten.
  encoding(ts, line, pc, block, encoding)
      each optimistic integer op the first time it runs: the block it is
      laid out in, and whether it computes in the `integer` or the `double`
      encoding, as its result fits or not then.
  unreachable(ts, line, reached, dropped, waiting, kept_by, at)
      after a forced thunk, for the rebuilds whose replaced code nothing
      running is in: how many blocks that code reached, those of them no
      longer reachable, whose versions are forgotten once their point needs
      the room (`evicted`), how many rebuilds are
      still waiting, how many of the reached blocks each kind of root keeps
      (the running code, the rebuilt blocks), and the block running.
  widen(ts, line, slot, block, origins, queued)
      each constant a fact says a slot holds widened to a double where
      `block` is compiled: the fact's origins (block@offset, ` rebuilt` if
      one already was), and whether a contraction loading it as a double
      was queued.
  contract_deferred(ts, line, origins, at)
      a queued contraction waiting, as the interpreter (in block `at`) or a
      frame returning will run code past where an origin introduced its fact.
  evicted(ts, line, pc, blocks)
      the version at a point the trimming found unreachable forgotten, the
      oldest, as the point has all the versions it can have.
  contract_refused(ts, line, origins, how, reason)
      a queued contraction dropped: a fact `used` since, an origin `compiled`,
      or every origin `rebuilt` already.
  inline(ts, line, callee, after, call_block, shift, entry, context)
      a call in the function at `line` inlined, its continuation at pc `after`,
      of the function defined at `callee`: the call's block, the block moving
      to the callee's frame, and the callee's entry block and its context.
  inline_cost(ts, line, callee, entry, blocks, cost, reused, inlines, why)
      each call a continuation measures for inlining: the function at
      `line`'s call of the function defined at `callee`, whose version
      `entry` the call ran, the blocks of it reaching the return the call
      took, what they cost and how many of their guards inlining lets the
      caller's facts stand for, and whether it inlines; `why` is
      `measured`, or why it wasn't: its code to the return `loops`, or none
      of it from `entry` is compiled as it ran (`unmeasured`).
  inline_return(ts, line, callee, after, block, context)
      the code after an inlined call, of the function at `line` at pc `after`,
      for a return in the inlined callee's code: its block and context.

    tools/trace_sql.py [--trace working/lunacy.fxt] QUERY
(in the devshell, whose `trace_processor_shell` it runs; `just trace-sql`)
"""
import argparse
import shutil
from perfetto.trace_processor import TraceProcessor, TraceProcessorConfig

VIEWS = {
    'spec_version': ['line', 'pc', 'outcome', 'block', 'versions', 'context', 'joined', 'shapes_dropped', 'origins'],
    'spec_block': ['block', 'line', 'pc', 'context'],
    'block_summary': ['block', 'line', 'pc', 'residuals', 'code', 'context', 'hotness', 'jitted', 'returns', 'returned_from', 'unreachable'],
    'alloc_step': ['trace', 'step', 'line', 'block', 'pc', 'off'],
    'alloc_start': ['trace', 'step', 'rise', 'arrives', 'worth', 'entry'],
    'alloc_op': ['trace', 'step', 'name', 'before', 'worth', 'skip', 'emits', 'after'],
    'contractible': ['line', 'pc', 'duplicates', 'origins', 'context', 'theirs'],
    'contract': ['line', 'origins', 'how', 'offsets', 'forgotten'],
    'contract_deferred': ['line', 'origins', 'at'],
    'contract_refused': ['line', 'origins', 'how', 'reason'],
    'unreachable': ['line', 'reached', 'dropped', 'waiting', 'kept_by', 'at'],
    'encoding': ['line', 'pc', 'block', 'encoding'],
    'widen': ['line', 'slot', 'block', 'origins', 'queued'],
    'evicted': ['line', 'pc', 'blocks'],
    'inline': ['line', 'callee', 'after', 'call_block', 'shift', 'entry', 'context'],
    'inline_return': ['line', 'callee', 'after', 'block', 'context'],
    'inline_cost': ['line', 'callee', 'entry', 'blocks', 'cost', 'reused', 'inlines', 'why'],
    'inline_refused': ['line', 'callee', 'call_block', 'reason'],
}
EVENTS = {'spec_version': ('spec', 'version'), 'spec_block': ('spec', 'block'), 'block_summary': ('spec', 'block_summary'),
          'alloc_step': ('alloc', 'step'), 'alloc_start': ('alloc', 'start'), 'alloc_op': ('alloc', 'op'),
          'contractible': ('spec', 'contractible'), 'contract': ('spec', 'contract'),
          'contract_deferred': ('spec', 'contract_deferred'), 'contract_refused': ('spec', 'contract_refused'),
          'unreachable': ('spec', 'unreachable'), 'encoding': ('spec', 'encoding'),
          'widen': ('spec', 'widen'), 'evicted': ('spec', 'evicted'),
          'inline': ('spec', 'inline'), 'inline_return': ('spec', 'inline_return'),
          'inline_cost': ('spec', 'inline_cost'), 'inline_refused': ('spec', 'inline_refused')}


def connect(trace):
    """A trace processor on `trace`, with the views above."""
    tp = TraceProcessor(trace=trace, config=TraceProcessorConfig(bin_path=shutil.which('trace_processor_shell')))
    for view, columns in VIEWS.items():
        extracted = ', '.join(f"EXTRACT_ARG(arg_set_id, '{c}') AS {c}" for c in columns)
        category, name = EVENTS[view]
        tp.query(f"CREATE PERFETTO VIEW {view} AS SELECT ts, {extracted} FROM slice "
                 f"WHERE category = '{category}' AND name = '{name}'")
    fates(tp)
    return tp


def ids(text):
    """The block ids of a comma separated list."""
    return [int(i) for i in str(text or '').split(',') if i.strip().isdigit()]


def fates(tp):
    """The `version_fate` table and its `point_versions` summary: each version's
    fate, found from the events forgetting versions, within its block id's life."""
    created = [(r.ts, r.block, r.line, r.pc) for r in tp.query("SELECT ts, block, line, pc FROM spec_block ORDER BY ts")]
    if not created:
        return
    # Each block id's events forgetting its version, in time order.
    ends = {}
    for r in tp.query("SELECT ts, forgotten FROM contract"):
        for block in ids(r.forgotten):
            ends.setdefault(block, []).append((r.ts, 'forgotten'))
    for r in tp.query("SELECT ts, blocks FROM evicted"):
        for block in ids(r.blocks):
            ends.setdefault(block, []).append((r.ts, 'evicted'))
    unreachable = {r.block for r in tp.query("SELECT block FROM block_summary WHERE unreachable = 1")}
    # When each block id's next version is created.
    following = {}
    last = {}
    for i, (ts, block, _, _) in enumerate(created):
        if block in last:
            following[last[block]] = ts
        last[block] = i
    rows = []
    for i, (ts, block, line, pc) in enumerate(created):
        until = following.get(i)
        end = next(((at, fate) for at, fate in sorted(ends.get(block, [])) if at >= ts and (until is None or at < until)), None)
        if end:
            fate, at = end[1], end[0]
        elif until is not None:
            fate, at = 'forgotten', until
        else:
            fate, at = ('unreachable' if block in unreachable else 'live'), None
        rows.append(f"({ts}, {block}, {line}, {pc}, '{fate}', {'NULL' if at is None else at})")
    tp.query("CREATE PERFETTO TABLE version_fate AS WITH fates(ts, block, line, pc, fate, at) AS "
             f"(VALUES {', '.join(rows)}) SELECT * FROM fates")
    tp.query("CREATE PERFETTO VIEW point_versions AS SELECT line, pc, COUNT(*) AS created, "
             "SUM(fate = 'live') AS live, SUM(fate = 'unreachable') AS unreachable, "
             "SUM(fate = 'evicted') AS evicted, SUM(fate = 'forgotten') AS forgotten "
             "FROM version_fate GROUP BY line, pc")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('query')
    ap.add_argument('--trace', default='working/lunacy.fxt')
    args = ap.parse_args()

    result = connect(args.trace).query(args.query)
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
