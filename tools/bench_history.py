#!/usr/bin/env python3
"""Benchmark times across commits: record hyperfine runs, report and plot them.

`record` appends a hyperfine `--export-json` file's results to the history
(bench/history.jsonl), one line per command: the benchmark, its argument, the
build the command ran (named by the command's hyperfine name: `release`,
`unsafe`, `interpreter`, `lua5.1`, ...; a `ref ` prefix is revision `--ref`'s)
and the commit it was built from, or, for this checkout with uncommitted
changes to what builds it, its HEAD marked dirty. A run over a `padding`
parameter (`just hyperfine-padding`: the build at each `LUNACY_JIT_PADDING`) is
one line per build, named `<build> padded`: its times are every padding's,
pooled, so its box and whiskers span where the JIT's code lands, and
`paddings` keeps each padding's own. A commit and build recorded again keeps
every line, and what reads the history pools them, as one result of all their
runs; a dirty HEAD's newest line stands alone, as it may be of other changes.

`report` prints, per benchmark and build, the latest commit's time, the
current dirty one's, the best and the first recorded, flagging a time worse
than the best or the commit before it by more than noise. `plot` writes the
same history as an HTML page of charts, one per benchmark (working/history.html):
each commit's runs as a box and whiskers per build, in commit order, and the
dirty ones apart, with the JIT code size of each commit on a second axis.
`vs` compares two revisions' pooled times on one build, benchmark by benchmark.
`attach-times` adds the runs' times to results recorded without them, from the
hyperfine exports they came from.

`record-size` appends the JIT code size of a benchmark's run to the size history
(bench/jit_sizes.jsonl), keyed as the times are: every byte of code the JIT
committed, from the section headers of the run's annotated disassembly (`just
jit-disasm`, working/jit_disasm.txt), which the unsafe build commits the same.
"""
import argparse
import datetime
import html
import json
import os
import re
import statistics
import subprocess
import sys
from collections import defaultdict

HISTORY = 'bench/history.jsonl'
SIZES = 'bench/jit_sizes.jsonl'
# A section of committed code in an annotated disassembly, and its bytes.
SECTION = re.compile(r'^==== .* @ 0x[0-9a-f]+, (\d+) bytes$')
SIZE_COLOR = '#ff7f0e'
PAGE = 'working/history.html'
# What builds the benchmarked binaries: a change elsewhere doesn't make a run
# dirty.
BUILD_PATHS = ['src', 'Cargo.toml', 'Cargo.lock', 'build.rs']
# Builds of this project, in the order reports list them.
BUILDS = ['unsafe', 'unsafe padded', 'release', 'interpreter']
# The builds a chart is scaled to and draws across commits; the rest (the
# interpreter, other Luas), an order of magnitude apart, as reference lines of
# their latest times where they fit.
CHARTED = ['unsafe', 'unsafe padded', 'release']
COLORS = {'unsafe': '#d62728', 'unsafe padded': '#ff9896', 'release': '#1f77b4', 'interpreter': '#7f7f7f',
          'lua5.1': '#2ca02c', 'lua5.5': '#17becf', 'luau': '#bcbd22', 'luau --codegen': '#e377c2', 'luajit -joff': '#9467bd', 'luajit': '#8c564b'}


def git(*args):
    return subprocess.run(['git', *args], capture_output=True, text=True, check=True).stdout.strip()


def head_state():
    """This checkout's HEAD, and whether what builds it differs from it."""
    head = git('rev-parse', 'HEAD')
    paths = [p for p in BUILD_PATHS if os.path.exists(p)]
    dirty = subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', *paths]).returncode != 0
    return head, dirty


def commit_info(rev):
    """A commit's hash, time and subject, or None for a revision git lacks."""
    try:
        sha, when, subject = git('show', '-s', '--format=%H%x00%ct%x00%s', rev).split('\0')
    except subprocess.CalledProcessError:
        return None
    return sha, int(when), subject


def load(path=HISTORY):
    if not os.path.exists(path):
        return []
    with open(path) as f:
        return [json.loads(line) for line in f if line.strip()]


def record(args):
    head, dirty = head_state()
    ref = commit_info(args.ref)[0] if args.ref else None
    results = json.load(open(args.json))['results']
    now = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds')
    lines = []
    # (commit, dirty, build) -> padding -> its times, of a run over paddings.
    padded = defaultdict(dict)
    for r in results:
        name = r['command']
        failed = [code for code in r.get('exit_codes', []) if code != 0]
        if failed:
            print(f'skipped {args.benchmark} {args.arg} {name}: exit code {failed[0]}', file=sys.stderr)
            continue
        if 'padding' in r.get('parameters', {}):
            # The build is the binary's directory; revision `--ref`'s is under
            # target/compare.
            exe = r['parameters'].get('build', './target/unsafe/bench')
            of_ref = exe.startswith('target/compare/')
            if of_ref and ref is None:
                sys.exit(f'{name}: a ref command, but no --ref')
            at = (ref, False) if of_ref else (head, dirty)
            padded[(*at, os.path.basename(os.path.dirname(exe)) + ' padded')][r['parameters']['padding']] = r['times']
            continue
        if name.startswith('ref '):
            if ref is None:
                sys.exit(f'{name}: a ref command, but no --ref')
            build, commit, is_dirty = name[len('ref '):], ref, False
        else:
            build, commit, is_dirty = name, head, dirty
        times = r['times']
        lines.append({
            'date': now, 'commit': commit, 'dirty': is_dirty,
            'benchmark': args.benchmark, 'arg': args.arg, 'build': build,
            'mean': r['mean'], 'stddev': r['stddev'], 'median': r['median'],
            'min': r['min'], 'max': r['max'], 'runs': len(times), 'times': times,
        })
    for (commit, is_dirty, build), paddings in padded.items():
        times = [t for runs in paddings.values() for t in runs]
        lines.append({
            'date': now, 'commit': commit, 'dirty': is_dirty,
            'benchmark': args.benchmark, 'arg': args.arg, 'build': build,
            'mean': statistics.mean(times), 'stddev': statistics.stdev(times), 'median': statistics.median(times),
            'min': min(times), 'max': max(times), 'runs': len(times), 'times': times, 'paddings': paddings,
        })
    os.makedirs(os.path.dirname(HISTORY), exist_ok=True)
    with open(HISTORY, 'a') as f:
        for line in lines:
            f.write(json.dumps(line, sort_keys=True) + '\n')
    for line in lines:
        mark = ' (dirty)' if line['dirty'] else ''
        print(f"recorded {line['benchmark']} {line['arg']} {line['build']} @ {line['commit'][:8]}{mark}: {line['mean']:.4f} s")


def record_size(args):
    head, dirty = (commit_info(args.ref)[0], False) if args.ref else head_state()
    sections = [int(m.group(1)) for line in open(args.disasm) if (m := SECTION.match(line.rstrip('\n')))]
    if not sections:
        sys.exit(f'{args.disasm}: no committed code')
    line = {
        'date': datetime.datetime.now(datetime.timezone.utc).isoformat(timespec='seconds'),
        'commit': head, 'dirty': dirty, 'benchmark': args.benchmark, 'arg': args.arg,
        'build': 'unsafe', 'bytes': sum(sections), 'sections': len(sections),
    }
    os.makedirs(os.path.dirname(SIZES), exist_ok=True)
    with open(SIZES, 'a') as f:
        f.write(json.dumps(line, sort_keys=True) + '\n')
    mark = ' (dirty)' if dirty else ''
    print(f"recorded {args.benchmark} {args.arg} JIT code @ {head[:8]}{mark}: {line['bytes']} bytes")


def sizes(info):
    """(benchmark, arg) -> commit -> its newest clean code size, and the newest
    dirty size of HEAD, keyed 'dirty'. Adds the commits' info to `info`."""
    head, _ = head_state()
    out = defaultdict(dict)
    for r in load(SIZES):
        key = (r['benchmark'], r['arg'])
        if r['dirty']:
            if r['commit'] == head:
                out[key]['dirty'] = r
            continue
        if r['commit'] not in info and (i := commit_info(r['commit'])) is not None:
            info[r['commit']] = i
        out[key][r['commit']] = r
    return out


def sizes_vs(args):
    """Each benchmark's latest JIT code size for revision `ref` and for this
    checkout (its dirty size, else HEAD's)."""
    ref = commit_info(args.ref)[0]
    head, _ = head_state()
    by_key = sizes({})
    print(f"{'benchmark':24} {args.ref[:10]:>10} {'this':>10} {'change':>8}")
    for (bench, arg) in sorted(by_key):
        at = by_key[(bench, arg)]
        old, new = at.get(ref), at.get('dirty', at.get(head))
        cells = [f"{r['bytes']:>10}" if r else f"{'-':>10}" for r in (old, new)]
        change = f"{(new['bytes'] / old['bytes'] - 1) * 100:+7.1f}%" if old and new else ''
        print(f"{bench + ' ' + arg:24} {cells[0]} {cells[1]} {change:>8}")


def times_vs(args):
    """Each benchmark's pooled time for revision `base` and for `head`, as `build`,
    fastest change first: their medians and its change, at how many paddings
    `head`'s median is the lower, whether their quartile boxes are apart; and the
    changes' geometric mean."""
    base, head = commit_info(args.base)[0], commit_info(args.head)[0]
    data, _ = series()
    rows = []
    for key, builds in data.items():
        old, new = builds.get(args.build, {}).get(base), builds.get(args.build, {}).get(head)
        if not (old and new):
            continue
        ob, nb = box(old), box(new)
        both = sorted(set(old.get('paddings', {})) & set(new.get('paddings', {})), key=int)
        wins = sum(statistics.median(new['paddings'][p]) < statistics.median(old['paddings'][p]) for p in both)
        apart = nb['q3'] < ob['q1'] or ob['q3'] < nb['q1']
        rows.append((nb['median'] / ob['median'] - 1, key, ob['median'], nb['median'],
                     f"{wins}/{len(both)}" if both else '', 'apart' if apart else 'overlap'))
    print(f"{'benchmark':24} {args.base[:10]:>10} {args.head[:10]:>10} {'change':>8} {'faster at':>9}  boxes")
    for change, (bench, arg), om, nm, wins, apart in sorted(rows):
        print(f"{bench + ' ' + arg:24} {om:10.4f} {nm:10.4f} {change * 100:+7.1f}% {wins:>9}  {apart}")
    if rows:
        geomean = statistics.geometric_mean([1 + r[0] for r in rows]) - 1
        print(f"geometric mean of {len(rows)}: {geomean * 100:+.2f}%")


def attach_times(args):
    """Add each hyperfine export's runs' times to the results recorded from it,
    which have its benchmark, argument, build and mean."""
    lines = load()
    attached = 0
    for path in args.json:
        for r in json.load(open(path))['results']:
            build = r['command'][len('ref '):] if r['command'].startswith('ref ') else r['command']
            for line in lines:
                if 'times' not in line and line['build'] == build and line['mean'] == r['mean'] \
                        and os.path.basename(path).startswith(f"hyperfine-{line['benchmark']}-{line['arg']}"):
                    line['times'] = r['times']
                    attached += 1
    with open(HISTORY, 'w') as f:
        for line in lines:
            f.write(json.dumps(line, sort_keys=True) + '\n')
    missing = sum('times' not in line for line in lines)
    print(f'attached {attached}; {missing} results without times')


def quantile(sorted_times, q):
    """The `q` quantile of `sorted_times`, interpolated linearly."""
    at = q * (len(sorted_times) - 1)
    below = int(at)
    above = min(below + 1, len(sorted_times) - 1)
    return sorted_times[below] + (sorted_times[above] - sorted_times[below]) * (at - below)


def box(r):
    """A result's box and whiskers: its quartiles, and the furthest runs within
    1.5 interquartile ranges of them (Tukey's), leaving out the runs past them.
    Without its runs' times, its mean and a standard deviation either side."""
    times = sorted(r.get('times') or [])
    if len(times) < 2:
        m, d = r['mean'], r['stddev']
        return {'q1': m - d, 'median': m, 'q3': m + d, 'lo': m - d, 'hi': m + d, 'outliers': 0}
    q1, median, q3 = quantile(times, 0.25), quantile(times, 0.5), quantile(times, 0.75)
    fence_lo, fence_hi = q1 - 1.5 * (q3 - q1), q3 + 1.5 * (q3 - q1)
    inside = [t for t in times if fence_lo <= t <= fence_hi]
    return {'q1': q1, 'median': median, 'q3': q3, 'lo': min(inside), 'hi': max(inside),
            'outliers': len(times) - len(inside)}


def pool(a, b):
    """One result of two of the same commit and build: their runs together, and
    over paddings each padding's runs together."""
    times = a['times'] + b['times']
    pooled = dict(b, times=times, runs=len(times), mean=statistics.mean(times),
                  stddev=statistics.stdev(times), median=statistics.median(times),
                  min=min(times), max=max(times))
    if 'paddings' in a or 'paddings' in b:
        paddings = defaultdict(list)
        for r in (a, b):
            for padding, runs in r.get('paddings', {}).items():
                paddings[padding] += runs
        pooled['paddings'] = dict(paddings)
    return pooled


def series():
    """(benchmark, arg) -> build -> commit -> all its clean results pooled, and
    the newest dirty result of HEAD, keyed 'dirty' (each dirty result may be of
    other changes); and the commits' info."""
    head, _ = head_state()
    out = defaultdict(lambda: defaultdict(dict))
    commits = {}
    for r in load():
        key = (r['benchmark'], r['arg'])
        if r['dirty']:
            if r['commit'] == head:
                out[key][r['build']]['dirty'] = r
            continue
        if r['commit'] not in commits:
            commits[r['commit']] = commit_info(r['commit'])
        runs = out[key][r['build']]
        runs[r['commit']] = pool(runs[r['commit']], r) if r['commit'] in runs else r
    return out, {c: i for c, i in commits.items() if i is not None}


def ordered(commits, info):
    return sorted((c for c in commits if c in info), key=lambda c: info[c][1])


def noise(a, b):
    """The difference two results may differ by as noise: twice their combined
    deviation, and at least 1% of the first."""
    return max(2 * (a['stddev'] ** 2 + b['stddev'] ** 2) ** 0.5, 0.01 * a['mean'])


def verdicts(runs, info):
    """The latest clean commit's result and the dirty one, each compared with the
    best clean result and the clean commit before it."""
    commits = ordered([c for c in runs if c != 'dirty'], info)
    rows = []
    if not commits:
        return commits, rows
    best = min(commits, key=lambda c: runs[c]['mean'])
    checks = [('latest', commits[-1], commits[-2] if len(commits) > 1 else None)]
    if 'dirty' in runs:
        checks.append(('dirty', 'dirty', commits[-1]))
    for label, at, before in checks:
        r = runs[at]
        flags = []
        if at != best and r['mean'] - runs[best]['mean'] > noise(runs[best], r):
            flags.append(f"{(r['mean'] / runs[best]['mean'] - 1) * 100:+.1f}% vs best {best[:8]}")
        if before and r['mean'] - runs[before]['mean'] > noise(runs[before], r):
            flags.append(f"{(r['mean'] / runs[before]['mean'] - 1) * 100:+.1f}% vs {before[:8]}")
        rows.append((label, at, r, flags))
    return commits, rows


def report(args):
    data, info = series()
    regressed = False
    for (bench, arg) in sorted(data):
        print(f'== {bench} {arg}')
        for build in BUILDS + sorted(set(data[(bench, arg)]) - set(BUILDS)):
            runs = data[(bench, arg)].get(build)
            if not runs:
                continue
            commits, rows = verdicts(runs, info)
            if not commits:
                continue
            first, best = commits[0], min(commits, key=lambda c: runs[c]['mean'])
            summary = (f"  {build:13} first {runs[first]['mean']:.4f} ({first[:8]})  "
                       f"best {runs[best]['mean']:.4f} ({best[:8]})")
            for label, at, r, flags in rows:
                where = 'dirty' if at == 'dirty' else at[:8]
                summary += f"  {label} {r['mean']:.4f} ± {r['stddev']:.4f} ({where})"
                if flags:
                    regressed = True
                    summary += '  REGRESSED ' + '; '.join(flags)
            print(summary)
    return 1 if regressed and args.strict else 0


def table(args):
    """Every commit's time for one build, a column per benchmark, in commit
    order, the dirty times last."""
    data, info = series()
    keys = sorted(k for k in data if args.build in data[k])
    commits = ordered({c for k in keys for c in data[k][args.build] if c != 'dirty'}, info)
    if any('dirty' in data[k][args.build] for k in keys):
        commits.append('dirty')
    print(f"{args.build:9}" + ''.join(f'{b[:12] + " " + a:>20}' for b, a in keys))
    for c in commits:
        cells = ''.join(f"{data[k][args.build][c]['mean']:>20.4f}" if c in data[k][args.build] else f'{"-":>20}' for k in keys)
        subject = '' if c == 'dirty' else info[c][2][:60]
        print(f"{'dirty' if c == 'dirty' else c[:8]:9}{cells}  {subject}")


def chart(bench, arg, runs_by_build, sizes_by_commit, info):
    """One benchmark's chart, as SVG: commits left to right, dirty last, each
    column a box and whiskers per charted build, their medians joined, and the
    JIT code size, on the right axis, as points joined."""
    commits = ordered({c for runs in [*runs_by_build.values(), sizes_by_commit] for c in runs if c != 'dirty'}, info)
    has_dirty = any('dirty' in runs for runs in [*runs_by_build.values(), sizes_by_commit])
    columns = commits + (['dirty'] if has_dirty else [])
    if not columns:
        return ''
    boxes = {build: {c: box(r) for c, r in runs_by_build.get(build, {}).items()} for build in CHARTED}
    values = [v for bs in boxes.values() for b in bs.values() for v in (b['lo'], b['hi'])]
    if not values:
        return ''
    lo, hi = min(values), max(values)
    lo, hi = lo - 0.05 * (hi - lo or hi), hi + 0.05 * (hi - lo or hi)
    width, height, left, right, top, bottom = 900, 320, 70, 230, 20, 90
    step = (width - left - right) / max(len(columns) - 1, 1)
    x = lambda i: left + i * step if len(columns) > 1 else left + (width - left - right) / 2
    y = lambda v: top + (hi - v) / (hi - lo) * (height - top - bottom)
    # The legend, right of the code size axis.
    legend_x = width - right + 72
    half = min(5.0, step / (2 * len(CHARTED) + 1))
    offset = {build: (k - (len(CHARTED) - 1) / 2) * 2.4 * half for k, build in enumerate(CHARTED)}
    parts = [f'<svg viewBox="0 0 {width} {height}" width="100%" role="img" aria-label="{html.escape(bench)} {arg}">']
    for k in range(5):
        v = lo + (hi - lo) * k / 4
        parts.append(f'<line x1="{left}" x2="{width - right}" y1="{y(v):.1f}" y2="{y(v):.1f}" class="grid"/>')
        parts.append(f'<text x="{left - 6}" y="{y(v) + 4:.1f}" text-anchor="end" class="axis">{v:.3f}s</text>')
    for i, c in enumerate(columns):
        label = 'dirty' if c == 'dirty' else c[:8]
        title = 'uncommitted changes on HEAD' if c == 'dirty' else f'{c[:8]} {info[c][2]}'
        parts.append(f'<text transform="translate({x(i):.1f},{height - bottom + 12}) rotate(45)" class="axis"><title>{html.escape(title)}</title>{label}</text>')
    legend = 0
    for build in CHARTED:
        bs = boxes[build]
        if not bs:
            continue
        color = COLORS.get(build, '#000')
        medians = [(x(i) + offset[build], y(bs[c]['median'])) for i, c in enumerate(commits) if c in bs]
        if len(medians) > 1:
            path = ' '.join(f'{px:.1f},{py:.1f}' for px, py in medians)
            parts.append(f'<polyline points="{path}" fill="none" stroke="{color}" stroke-opacity="0.5" stroke-width="{1.5 if build == "unsafe" else 1}"/>')
        for i, c in enumerate(columns):
            if c not in bs:
                continue
            b, r, cx = bs[c], runs_by_build[build][c], x(i) + offset[build]
            dirty = c == 'dirty'
            fill = 'none' if dirty else color
            tip = (f"{build}{' dirty' if dirty else ''}: median {b['median']:.4f}, quartiles {b['q1']:.4f}–{b['q3']:.4f}, "
                   f"whiskers {b['lo']:.4f}–{b['hi']:.4f} s, mean {r['mean']:.4f} ± {r['stddev']:.4f}, "
                   f"{r['runs']} runs, {b['outliers']} outliers left out")
            parts.append(f'<g><title>{html.escape(tip)}</title>'
                         f'<line x1="{cx:.1f}" x2="{cx:.1f}" y1="{y(b["hi"]):.1f}" y2="{y(b["q3"]):.1f}" stroke="{color}"/>'
                         f'<line x1="{cx:.1f}" x2="{cx:.1f}" y1="{y(b["q1"]):.1f}" y2="{y(b["lo"]):.1f}" stroke="{color}"/>'
                         f'<line x1="{cx - half / 2:.1f}" x2="{cx + half / 2:.1f}" y1="{y(b["hi"]):.1f}" y2="{y(b["hi"]):.1f}" stroke="{color}"/>'
                         f'<line x1="{cx - half / 2:.1f}" x2="{cx + half / 2:.1f}" y1="{y(b["lo"]):.1f}" y2="{y(b["lo"]):.1f}" stroke="{color}"/>'
                         f'<rect x="{cx - half:.1f}" y="{y(b["q3"]):.1f}" width="{2 * half:.1f}" height="{max(y(b["q1"]) - y(b["q3"]), 1):.1f}" '
                         f'fill="{fill}" fill-opacity="0.35" stroke="{color}" stroke-width="{2 if dirty else 1}"/>'
                         f'<line x1="{cx - half:.1f}" x2="{cx + half:.1f}" y1="{y(b["median"]):.1f}" y2="{y(b["median"]):.1f}" stroke="{color}" stroke-width="2"/></g>')
        parts.append(f'<rect x="{legend_x}" y="{top + legend * 18}" width="10" height="10" fill="{color}"/>')
        parts.append(f'<text x="{legend_x + 16}" y="{top + legend * 18 + 9}" class="axis">{html.escape(build)}</text>')
        legend += 1
    for build in sorted(set(runs_by_build) - set(CHARTED), key=lambda b: (b not in BUILDS, b)):
        runs = runs_by_build[build]
        color = COLORS.get(build, '#000')
        latest = [c for c in commits if c in runs]
        r = runs['dirty'] if 'dirty' in runs else runs[latest[-1]] if latest else None
        if r is None:
            continue
        median = box(r)['median']
        label = f'{build} {median:.3f}s'
        if lo <= median <= hi:
            parts.append(f'<line x1="{left}" x2="{width - right}" y1="{y(median):.1f}" y2="{y(median):.1f}" stroke="{color}" stroke-dasharray="4 3"><title>{build} median {median:.4f} s</title></line>')
        else:
            label += ' ↑' if median > hi else ' ↓'
        parts.append(f'<rect x="{legend_x}" y="{top + legend * 18}" width="10" height="10" fill="{color}"/>')
        parts.append(f'<text x="{legend_x + 16}" y="{top + legend * 18 + 9}" class="axis">{html.escape(label)}</text>')
        legend += 1
    if sizes_by_commit:
        size_values = [r['bytes'] for r in sizes_by_commit.values()]
        size_lo, size_hi = min(size_values), max(size_values)
        pad = 0.05 * (size_hi - size_lo or size_hi)
        size_lo, size_hi = max(size_lo - pad, 0), size_hi + pad
        size_y = lambda v: top + (size_hi - v) / (size_hi - size_lo) * (height - top - bottom)
        for k in range(5):
            v = size_lo + (size_hi - size_lo) * k / 4
            parts.append(f'<text x="{width - right + 6}" y="{size_y(v) + 4:.1f}" class="axis size">{v / 1024:.1f} KiB</text>')
        points = [(x(i), size_y(sizes_by_commit[c]['bytes'])) for i, c in enumerate(commits) if c in sizes_by_commit]
        if len(points) > 1:
            path = ' '.join(f'{px:.1f},{py:.1f}' for px, py in points)
            parts.append(f'<polyline points="{path}" fill="none" stroke="{SIZE_COLOR}" stroke-opacity="0.6" stroke-dasharray="2 2"/>')
        for i, c in enumerate(columns):
            if c not in sizes_by_commit:
                continue
            r = sizes_by_commit[c]
            tip = f"JIT code{' dirty' if c == 'dirty' else ''}: {r['bytes']} bytes in {r['sections']} sections"
            fill = 'none' if c == 'dirty' else SIZE_COLOR
            parts.append(f'<circle cx="{x(i):.1f}" cy="{size_y(r["bytes"]):.1f}" r="3.5" fill="{fill}" stroke="{SIZE_COLOR}"><title>{html.escape(tip)}</title></circle>')
        parts.append(f'<rect x="{legend_x}" y="{top + legend * 18}" width="10" height="10" fill="{SIZE_COLOR}"/>')
        parts.append(f'<text x="{legend_x + 16}" y="{top + legend * 18 + 9}" class="axis">JIT code (right)</text>')
        legend += 1
    parts.append('</svg>')
    return '\n'.join(parts)


def plot(args):
    data, info = series()
    code = sizes(info)
    sections = []
    for (bench, arg) in sorted(data):
        rows = []
        for build in BUILDS:
            runs = data[(bench, arg)].get(build)
            if not runs:
                continue
            _, checks = verdicts(runs, info)
            for label, at, r, flags in checks:
                where = 'dirty' if at == 'dirty' else at[:8]
                status = '<span class="bad">' + html.escape('; '.join(flags)) + '</span>' if flags else 'ok'
                rows.append(f'<tr><td>{build}</td><td>{label} ({where})</td><td>{r["mean"]:.4f} ± {r["stddev"]:.4f}</td><td>{status}</td></tr>')
        sections.append(f'<section><h2>{html.escape(bench)} {html.escape(arg)}</h2>{chart(bench, arg, data[(bench, arg)], code.get((bench, arg), {}), info)}'
                        f'<table><tr><th>build</th><th>at</th><th>mean (s)</th><th>vs best, vs previous</th></tr>{"".join(rows)}</table></section>')
    page = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Benchmark History</title>
<style>
:root {{ --bg: #fff; --fg: #111; --grid: #e5e5e5; --bad: #c00; }}
@media (prefers-color-scheme: dark) {{ :root:not([data-theme="light"]) {{ --bg: #111; --fg: #eee; --grid: #333; --bad: #f66; }} }}
:root[data-theme="dark"] {{ --bg: #111; --fg: #eee; --grid: #333; --bad: #f66; }}
body {{ background: var(--bg); color: var(--fg); font: 14px system-ui, sans-serif; margin: 0 auto; max-width: 960px; padding: 0 16px; }}
.grid {{ stroke: var(--grid); }} .axis {{ fill: var(--fg); font-size: 11px; }}
table {{ border-collapse: collapse; margin: 8px 0 24px; }} td, th {{ padding: 2px 10px; text-align: left; }}
.bad {{ color: var(--bad); font-weight: 600; }} .size {{ fill: {SIZE_COLOR}; }}
</style></head><body>
<h1>Benchmark history</h1>
<p>Each commit's runs of the unsafe and release builds, in commit order, and of the unsafe build over JIT paddings (its runs at every <code>LUNACY_JIT_PADDING</code> pooled, so its spread is what the code's placement alone does): the box spans the quartiles, the bar in it is the median, and the whiskers reach the furthest runs within 1.5 interquartile ranges (runs past them are left out, and counted in the tooltip); a line joins the medians. The hollow box is HEAD with uncommitted changes. Unsafe is the build that matters. The interpreter and other Luas are dashed lines of their latest medians, or in the legend alone, marked ↑ or ↓, off the chart's scale. The orange points, on the right axis, are each commit's JIT code size for the benchmark (the hollow one HEAD with uncommitted changes).</p>
{"".join(sections)}
</body></html>
'''
    os.makedirs(os.path.dirname(args.out) or '.', exist_ok=True)
    with open(args.out, 'w') as f:
        f.write(page)
    print(args.out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)
    r = sub.add_parser('record', help='append a hyperfine JSON export to the history')
    r.add_argument('json')
    r.add_argument('--benchmark', required=True)
    r.add_argument('--arg', required=True, help="the benchmark's argument (`times`)")
    r.add_argument('--ref', help="the revision `ref `-prefixed commands were built from")
    r.set_defaults(func=record)
    p = sub.add_parser('report', help='print each benchmark and build, flagging regressions')
    p.add_argument('--strict', action='store_true', help='exit 1 on a regression')
    p.set_defaults(func=report)
    z = sub.add_parser('record-size', help="append a run's JIT code size to the size history")
    z.add_argument('disasm', help="the run's annotated disassembly (`just jit-disasm`)")
    z.add_argument('--benchmark', required=True)
    z.add_argument('--arg', required=True, help="the benchmark's argument (`times`)")
    z.add_argument('--ref', help='the revision that ran, if not this checkout')
    z.set_defaults(func=record_size)
    v = sub.add_parser('sizes-vs', help="this checkout's JIT code sizes against a revision's")
    v.add_argument('ref')
    v.set_defaults(func=sizes_vs)
    w = sub.add_parser('vs', help="one revision's times against another's, every run of each pooled")
    w.add_argument('base')
    w.add_argument('head')
    w.add_argument('--build', default='unsafe padded')
    w.set_defaults(func=times_vs)
    a = sub.add_parser('attach-times', help='add the runs\' times to results recorded without them')
    a.add_argument('json', nargs='+', help='the hyperfine exports they were recorded from')
    a.set_defaults(func=attach_times)
    t = sub.add_parser('table', help="every commit's time for one build, a column per benchmark")
    t.add_argument('--build', default='unsafe')
    t.set_defaults(func=table)
    g = sub.add_parser('plot', help='write the history as an HTML page of charts')
    g.add_argument('--out', default=PAGE)
    g.set_defaults(func=plot)
    args = ap.parse_args()
    return args.func(args)


if __name__ == '__main__':
    sys.exit(main())
