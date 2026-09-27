#!/usr/bin/env python3
"""The latest benchmark times as one grouped bar chart, as compiler papers draw
them: a group of bars per benchmark, one per implementation (lua5.1, lua5.5,
LuaJIT without and with its JIT, and this project's interpreter, release and
unsafe builds), on one linear axis of seconds.

Each bar is the median of its runs, with a whisker across their quartiles,
from the most recent clean commit the history (bench/history.jsonl, see
tools/bench_history.py) has that build's time at; a build without one (lua5.1
and lua5.5 lack the bit library some benchmarks use) is marked n/a. `--builds`
picks the implementations (the interpreter's times, an order of magnitude past
the rest, set the scale when it's drawn); `--clamp`'s (lua5.1 and lua5.5 by
default) don't set it past 1.5 times the rest's highest, a bar past the top cut
under a hat with its time. Writes working/bars.html.
"""
import argparse
import html
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from bench_history import box, series, ordered, COLORS  # noqa: E402

ORDER = ['lua5.1', 'lua5.5', 'luajit -joff', 'luajit', 'interpreter', 'release', 'unsafe']
LABELS = {'luajit -joff': 'LuaJIT (interpreter)', 'luajit': 'LuaJIT', 'lua5.1': 'Lua 5.1', 'lua5.5': 'Lua 5.5',
          'interpreter': 'lunacy interpreter', 'release': 'lunacy release', 'unsafe': 'lunacy unsafe'}


def latest(runs, info):
    """A build's newest clean result, and its commit."""
    commits = ordered([c for c in runs if c != 'dirty'], info)
    return (runs[commits[-1]], commits[-1]) if commits else (None, None)


def nice_step(span):
    """A round tick step (1, 2, 2.5 or 5 times a power of ten) giving at most
    five ticks over `span`."""
    raw = span / 5
    magnitude = 10 ** math.floor(math.log10(raw))
    return next(m * magnitude for m in (1, 2, 2.5, 5, 10) if raw <= m * magnitude)


def chart(data, info, builds, clamp):
    groups = []
    for bench, arg in sorted(data):
        bars = []
        for build in builds:
            r, commit = latest(data[(bench, arg)].get(build, {}), info)
            bars.append((build, r, commit, box(r) if r else None))
        groups.append((bench, arg, bars))
    # The clamped implementations' bars don't set the scale past 1.5 times the
    # highest of the rest: one past the chart's top is cut there, under a hat
    # with its time.
    scaled = [b['q3'] for _, _, bars in groups for build, _, _, b in bars if b and build not in clamp]
    clamped = [b['q3'] for _, _, bars in groups for build, _, _, b in bars if b and build in clamp]
    top_value = max(scaled + [min(max(clamped + [0]), 1.5 * max(scaled))]) if scaled else max(clamped)
    step = nice_step(top_value)
    hi = step * (int(top_value / step) + 1)
    bar_w, gap, left, right, top, bottom = 14, 22, 56, 16, 30, 58
    group_w = bar_w * len(builds)
    width = left + len(groups) * group_w + (len(groups) - 1) * gap + right
    height = 360
    y = lambda v: top + (hi - v) / hi * (height - top - bottom)
    parts = [f'<svg viewBox="0 0 {width} {height}" width="100%" role="img" aria-label="benchmark times">']
    for k in range(round(hi / step) + 1):
        t = k * step
        parts.append(f'<line x1="{left}" x2="{width - right}" y1="{y(t):.1f}" y2="{y(t):.1f}" class="grid"/>')
        parts.append(f'<text x="{left - 5}" y="{y(t) + 4:.1f}" text-anchor="end" class="axis">{t:g}s</text>')
    for g, (bench, arg, bars) in enumerate(groups):
        x0 = left + g * (group_w + gap)
        parts.append(f'<text x="{x0 + group_w / 2:.1f}" y="{height - bottom + 16}" text-anchor="middle" class="axis">{html.escape(bench)}</text>')
        parts.append(f'<text x="{x0 + group_w / 2:.1f}" y="{height - bottom + 29}" text-anchor="middle" class="axis">{html.escape(arg)}</text>')
        for k, (build, r, commit, b) in enumerate(bars):
            x = x0 + k * bar_w
            if not b:
                parts.append(f'<text x="{x + bar_w / 2:.1f}" y="{y(0) - 3:.1f}" text-anchor="middle" class="na">n/a</text>')
                continue
            tip = (f"{bench} {arg}, {LABELS.get(build, build)} @ {commit[:8]}: median {b['median']:.4f} s, "
                   f"quartiles {b['q1']:.4f}–{b['q3']:.4f} s, {r['runs']} runs")
            color = COLORS.get(build, "#555")
            if b['median'] > hi:
                hat = 6
                parts.append(f'<g><title>{html.escape(tip)}</title>'
                             f'<rect x="{x + 1:.1f}" y="{y(hi) + hat:.1f}" width="{bar_w - 2}" height="{y(0) - y(hi) - hat:.1f}" fill="{color}"/>'
                             f'<polygon points="{x + 1:.1f},{y(hi) + hat:.1f} {x + bar_w / 2:.1f},{y(hi):.1f} {x + bar_w - 1:.1f},{y(hi) + hat:.1f}" fill="{color}"/>'
                             f'<text x="{x + bar_w / 2:.1f}" y="{y(hi) - 3:.1f}" text-anchor="middle" class="value">{b["median"]:.3g}s</text></g>')
                continue
            parts.append(f'<g><title>{html.escape(tip)}</title>'
                         f'<rect x="{x + 1:.1f}" y="{y(b["median"]):.1f}" width="{bar_w - 2}" height="{max(y(0) - y(b["median"]), 0.5):.1f}" fill="{color}"/>'
                         f'<line x1="{x + bar_w / 2:.1f}" x2="{x + bar_w / 2:.1f}" y1="{y(min(b["q3"], hi)):.1f}" y2="{y(b["q1"]):.1f}" class="whisker"/></g>')
    parts.append(f'<line x1="{left}" x2="{width - right}" y1="{y(0):.1f}" y2="{y(0):.1f}" class="baseline"/>')
    legend_y = height - 12
    x = left
    for build in builds:
        parts.append(f'<rect x="{x}" y="{legend_y - 9}" width="10" height="10" fill="{COLORS.get(build, "#555")}"/>')
        label = LABELS.get(build, build)
        parts.append(f'<text x="{x + 14}" y="{legend_y}" class="axis">{html.escape(label)}</text>')
        x += 24 + 6.2 * len(label)
    parts.append('</svg>')
    return '\n'.join(parts)


def table(data, info, builds):
    rows = []
    for bench, arg in sorted(data):
        cells = []
        for build in builds:
            r, _ = latest(data[(bench, arg)].get(build, {}), info)
            cells.append(f'<td>{box(r)["median"]:.3f}</td>' if r else '<td>n/a</td>')
        rows.append(f'<tr><th>{html.escape(bench)} {html.escape(arg)}</th>{"".join(cells)}</tr>')
    head = ''.join(f'<th>{html.escape(LABELS.get(b, b))}</th>' for b in builds)
    return f'<table><tr><th>median (s)</th>{head}</tr>{"".join(rows)}</table>'


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--builds', default=','.join(ORDER), help='the implementations, comma separated, in bar order')
    ap.add_argument('--clamp', default='lua5.1,lua5.5', help="the implementations, comma separated, whose bars don't set the scale past 1.5 times the rest's highest")
    ap.add_argument('--out', default='working/bars.html')
    args = ap.parse_args()
    builds = args.builds.split(',')
    data, info = series()
    commits = sorted({latest(data[k].get(b, {}), info)[1] for k in data for b in builds} - {None}, key=lambda c: info[c][1])
    at = ', '.join(f'{c[:8]} ({html.escape(info[c][2])})' for c in commits)
    page = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Benchmark Times</title>
<style>
:root {{ --bg: #fff; --fg: #111; --grid: #e5e5e5; }}
@media (prefers-color-scheme: dark) {{ :root:not([data-theme="light"]) {{ --bg: #111; --fg: #eee; --grid: #333; }} }}
:root[data-theme="dark"] {{ --bg: #111; --fg: #eee; --grid: #333; }}
body {{ background: var(--bg); color: var(--fg); font: 14px system-ui, sans-serif; margin: 0 auto; max-width: 1200px; padding: 0 16px; }}
.grid {{ stroke: var(--grid); }} .baseline {{ stroke: var(--fg); }} .axis {{ fill: var(--fg); font-size: 11px; }}
.na {{ fill: var(--fg); font-size: 7px; }} .value {{ fill: var(--fg); font-size: 8px; }} .whisker {{ stroke: var(--fg); stroke-width: 1; }}
.scroll {{ overflow-x: auto; }} table {{ border-collapse: collapse; margin: 16px 0; }} td, th {{ padding: 2px 8px; text-align: right; }}
</style></head><body>
<h1>Benchmark times</h1>
<p>Median time per implementation, in seconds; whiskers span the quartiles. Each build's latest clean commit: {at}.</p>
<div class="scroll">{chart(data, info, builds, set(filter(None, args.clamp.split(','))))}</div>
<div class="scroll">{table(data, info, builds)}</div>
</body></html>
'''
    os.makedirs(os.path.dirname(args.out) or '.', exist_ok=True)
    with open(args.out, 'w') as f:
        f.write(page)
    print(args.out)


if __name__ == '__main__':
    sys.exit(main())
