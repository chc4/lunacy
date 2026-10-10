#!/usr/bin/env python3
"""Two runs' residual graphs (feature `graph`, as `just graph-golden` writes them)
side by side, as one HTML page: each run's last-written graph, which holds every
block the specializer made, rendered with graphviz, searchable and zoomable, over
a table of the blocks and the residuals whose counts differ between the runs.

    tools/graph_compare.py --before DIR --after DIR --out DIR
        [--before-label TEXT] [--after-label TEXT] [--title TEXT] [--about TEXT]

Writes DIR/index.html, DIR/before.svg and DIR/after.svg (in the devshell, which
has `dot`).
"""
import argparse
import collections
import html
import re
import subprocess
from pathlib import Path

NODE = re.compile(r'^\s*\d+\[id=\d+,shape=record,label="(\d+) x(\d+) \| \{(.*)\}"\]\s*$')


def last_graph(directory):
    """The run's last-written graph: each holds every block made so far."""
    graphs = sorted(Path(directory).glob('*.dot'), key=lambda p: p.stat().st_mtime)
    if not graphs:
        raise SystemExit(f'graph_compare: no .dot files in {directory}')
    return graphs[-1]


def counts(dot):
    """Blocks, blocks never entered, and how many of each residual the blocks have."""
    blocks, never = 0, 0
    residuals = collections.Counter()
    for line in dot.read_text().splitlines():
        m = NODE.match(line)
        if not m:
            continue
        blocks += 1
        never += m.group(2) == '0'
        fields = m.group(3).split('| ')
        # A version's first field is its pc and context.
        if fields and fields[0].lstrip().startswith('PC:'):
            fields = fields[1:]
        for field in fields:
            # A residual by its name, and its first argument where that names it (a window's
            # op, an exec's name), not where it is a number (a slot, a block, an address).
            m = re.match(r'\s*(\w+)(?:\((\w+))?', field)
            if m:
                residuals[m.group(1) + (f' {m.group(2)}' if m.group(2) and not m.group(2).isdigit() and not m.group(2).startswith('0x') else '')] += 1
    return blocks, never, residuals


def render(dot, svg):
    """`dot` as SVG at `svg`, without its DOCTYPE, which an artifact's files may not carry."""
    text = subprocess.run(['dot', '-Tsvg', str(dot)], check=True, capture_output=True, text=True).stdout
    svg.write_text(re.sub(r'<!DOCTYPE[^>]*>\s*', '', text))


def rows(before, after):
    """The table's rows: blocks, then each residual whose count differs, most changed first."""
    (b_blocks, b_never, b_res), (a_blocks, a_never, a_res) = before, after
    out = [('Blocks', b_blocks, a_blocks), ('Never entered (x0)', b_never, a_never)]
    changed = [(name, b_res[name], a_res[name]) for name in set(b_res) | set(a_res) if b_res[name] != a_res[name]]
    changed.sort(key=lambda r: (-abs(r[2] - r[1]), r[0]))
    return out + changed


PAGE = """<title>{title}</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=IBM+Plex+Sans:wght@400;500;600&family=IBM+Plex+Mono:wght@400;500&display=swap">
<style>
/* Layout: a summary strip over two graph viewports, side by side when wide, stacked when narrow. */
:root {{
  --bg: #f3f4f1; --surface: #ffffff; --paper: #ffffff; --fg: #1c1f1d; --muted: #5e6660; --rule: #d6dad5;
  --accent: #2f6b4f; --before: #8a5a1f; --after: #2f6b4f; --hit: #f2c94c; --hit-current: #e8590c;
  --sans: "IBM Plex Sans", system-ui, -apple-system, "Segoe UI", sans-serif;
  --mono: "IBM Plex Mono", ui-monospace, "SFMono-Regular", Menlo, monospace;
}}
@media (prefers-color-scheme: dark) {{
  :root:not([data-theme="light"]) {{
    --bg: #141715; --surface: #1d211f; --paper: #f4f5f2; --fg: #e5e8e4; --muted: #9aa39c; --rule: #333a35;
    --accent: #7cc4a0; --before: #e0a85c; --after: #7cc4a0; --hit: #f2c94c; --hit-current: #ff7a2e; color-scheme: dark;
  }}
}}
:root[data-theme="dark"] {{
  --bg: #141715; --surface: #1d211f; --paper: #f4f5f2; --fg: #e5e8e4; --muted: #9aa39c; --rule: #333a35;
  --accent: #7cc4a0; --before: #e0a85c; --after: #7cc4a0; --hit: #f2c94c; --hit-current: #ff7a2e; color-scheme: dark;
}}
html, body {{ height: 100%; }}
body {{ background: var(--bg); color: var(--fg); font-family: var(--sans); font-size: 14px; padding-inline: 16px; padding-block: 16px;
  box-sizing: border-box; display: flex; flex-direction: column; gap: 14px; }}
h1 {{ font-size: 20px; font-weight: 600; margin: 0; text-wrap: balance; }}
.lede {{ margin: 4px 0 0; color: var(--muted); max-width: 72ch; line-height: 1.5; }}
code, .mono {{ font-family: var(--mono); font-size: 0.92em; }}
header {{ display: flex; flex-wrap: wrap; gap: 16px 32px; align-items: flex-end; justify-content: space-between; }}
.stats {{ border-collapse: collapse; font-variant-numeric: tabular-nums; font-size: 13px; }}
.stats th, .stats td {{ padding: 3px 10px; text-align: right; border-bottom: 1px solid var(--rule); }}
.stats th:first-child, .stats td:first-child {{ text-align: left; color: var(--muted); font-weight: 400; font-family: var(--mono); font-size: 12px; }}
.stats thead th {{ font-weight: 600; font-size: 12px; letter-spacing: 0.04em; text-transform: uppercase; }}
.stats .b {{ color: var(--before); }} .stats .a {{ color: var(--after); }}
.stats-wrap {{ overflow: auto; max-height: 34vh; }}
.controls {{ display: flex; flex-wrap: wrap; gap: 8px 14px; align-items: center; }}
.controls label {{ color: var(--muted); font-size: 12px; letter-spacing: 0.04em; text-transform: uppercase; }}
button, select, input[type="search"] {{ font: inherit; color: var(--fg); background: var(--surface); border: 1px solid var(--rule); border-radius: 4px; padding: 4px 9px; }}
button {{ cursor: pointer; }}
button:hover {{ border-color: var(--accent); }}
button:focus-visible, select:focus-visible, input:focus-visible {{ outline: 2px solid var(--accent); outline-offset: 1px; }}
.panes {{ flex: 1; min-height: 420px; display: grid; grid-template-columns: 1fr 1fr; gap: 14px; }}
@media (max-width: 900px) {{ .panes {{ grid-template-columns: 1fr; }} .pane {{ min-height: 60vh; }} }}
.pane {{ display: flex; flex-direction: column; min-width: 0; min-height: 0; background: var(--surface); border: 1px solid var(--rule); border-radius: 6px; }}
.pane-head {{ display: flex; flex-wrap: wrap; gap: 8px; align-items: center; padding: 8px 10px; border-bottom: 1px solid var(--rule); }}
.pane-head h2 {{ margin: 0; font-size: 14px; font-weight: 600; flex: 1 1 auto; }}
.pane-head h2 .tag {{ font-family: var(--mono); font-weight: 400; font-size: 12px; color: var(--muted); margin-left: 6px; }}
.pane[data-side="before"] h2 {{ color: var(--before); }}
.pane[data-side="after"] h2 {{ color: var(--after); }}
.pane-head input[type="search"] {{ width: 13em; max-width: 100%; }}
.count {{ font-family: var(--mono); font-size: 12px; color: var(--muted); min-width: 6ch; font-variant-numeric: tabular-nums; }}
.viewport {{ flex: 1; min-height: 0; overflow: auto; background: var(--paper); cursor: grab; border-radius: 0 0 6px 6px; }}
.viewport.dragging {{ cursor: grabbing; }}
.viewport svg {{ display: block; }}
.loading {{ padding: 24px; color: #5e6660; font-family: var(--mono); }}
.viewport .node.hit polygon, .viewport .node.hit path {{ fill: var(--hit) !important; }}
.viewport .node.hit-current polygon, .viewport .node.hit-current path {{ fill: var(--hit-current) !important; }}
.key {{ color: var(--muted); font-size: 12.5px; line-height: 1.5; }}
</style>

<header>
  <div>
    <h1>{title}</h1>
    <p class="lede">{about} Each side is the run's last graph, which holds every block the specializer made: its id, how many times it ran (<code>x2</code>), its pc and context if it is still a version, then its residuals.</p>
  </div>
  <div class="stats-wrap">
    <table class="stats" aria-label="Blocks and the residuals whose counts differ">
      <thead><tr><th></th><th class="b">{before_label}</th><th class="a">{after_label}</th></tr></thead>
      <tbody>
{rows}
      </tbody>
    </table>
  </div>
</header>

<div class="controls">
  <label for="zoom">Zoom</label>
  <select id="zoom">
    <option value="0.08">8%</option><option value="0.15">15%</option><option value="0.25" selected>25%</option>
    <option value="0.4">40%</option><option value="0.6">60%</option><option value="1">100%</option>
  </select>
  <span class="key">Drag a graph to pan. Search either side for a residual or a block id; Enter steps through the matches.</span>
</div>

<div class="panes">
  <section class="pane" data-side="before" aria-label="{before_label}">
    <div class="pane-head">
      <h2>{before_label}</h2>
      <input type="search" id="search-before" placeholder="Search blocks" aria-label="Search blocks, {before_label}">
      <button type="button" data-step="-1" data-side="before" aria-label="Previous match">&#8593;</button>
      <button type="button" data-step="1" data-side="before" aria-label="Next match">&#8595;</button>
      <span class="count" id="count-before"></span>
    </div>
    <div class="viewport" id="view-before"><div class="loading">Loading graph…</div></div>
  </section>
  <section class="pane" data-side="after" aria-label="{after_label}">
    <div class="pane-head">
      <h2>{after_label}</h2>
      <input type="search" id="search-after" placeholder="Search blocks" aria-label="Search blocks, {after_label}">
      <button type="button" data-step="-1" data-side="after" aria-label="Previous match">&#8593;</button>
      <button type="button" data-step="1" data-side="after" aria-label="Next match">&#8595;</button>
      <span class="count" id="count-after"></span>
    </div>
    <div class="viewport" id="view-after"><div class="loading">Loading graph…</div></div>
  </section>
</div>

<script>
(() => {{
  const sides = ["before", "after"];
  const state = {{ before: {{ svg: null, w: 0, h: 0, hits: [], at: -1 }}, after: {{ svg: null, w: 0, h: 0, hits: [], at: -1 }} }};
  const zoomSel = document.getElementById("zoom");
  const scale = () => parseFloat(zoomSel.value);
  function applyZoom(side) {{
    const s = state[side];
    if (!s.svg) return;
    s.svg.setAttribute("width", Math.round(s.w * scale()));
    s.svg.setAttribute("height", Math.round(s.h * scale()));
  }}
  function search(side) {{
    const s = state[side];
    if (!s.svg) return;
    const q = document.getElementById("search-" + side).value.trim().toLowerCase();
    s.svg.querySelectorAll(".node").forEach(n => n.classList.remove("hit", "hit-current"));
    s.hits = q ? [...s.svg.querySelectorAll(".node")].filter(n => n.textContent.toLowerCase().includes(q)) : [];
    s.hits.forEach(n => n.classList.add("hit"));
    s.at = -1;
    document.getElementById("count-" + side).textContent = q ? s.hits.length + " found" : "";
  }}
  function step(side, by) {{
    const s = state[side];
    if (!s.hits.length) return;
    if (s.at >= 0) s.hits[s.at].classList.remove("hit-current");
    s.at = (s.at + by + s.hits.length) % s.hits.length;
    const node = s.hits[s.at];
    node.classList.add("hit-current");
    const view = document.getElementById("view-" + side);
    const nb = node.getBoundingClientRect(), vb = view.getBoundingClientRect();
    view.scrollLeft += nb.left - vb.left - (vb.width - nb.width) / 2;
    view.scrollTop += nb.top - vb.top - (vb.height - nb.height) / 2;
    document.getElementById("count-" + side).textContent = (s.at + 1) + " / " + s.hits.length;
  }}
  async function load(side) {{
    const view = document.getElementById("view-" + side);
    try {{
      const text = await (await fetch(side + ".svg")).text();
      view.innerHTML = text.replace(/^[\\s\\S]*?(<svg)/, "$1");
      const svg = view.querySelector("svg");
      const vb = svg.viewBox.baseVal;
      state[side] = {{ svg, w: vb.width, h: vb.height, hits: [], at: -1 }};
      applyZoom(side);
      search(side);
    }} catch (e) {{
      view.innerHTML = '<div class="loading">The graph didn\\u2019t load: ' + String(e.message || e) + '</div>';
    }}
  }}
  zoomSel.addEventListener("change", () => sides.forEach(applyZoom));
  sides.forEach(side => {{
    const input = document.getElementById("search-" + side);
    input.addEventListener("input", () => search(side));
    input.addEventListener("keydown", e => {{ if (e.key === "Enter") step(side, e.shiftKey ? -1 : 1); }});
  }});
  document.querySelectorAll("button[data-step]").forEach(b => b.addEventListener("click", () => step(b.dataset.side, parseInt(b.dataset.step, 10))));
  document.querySelectorAll(".viewport").forEach(view => {{
    let drag = null;
    view.addEventListener("pointerdown", e => {{
      if (e.button !== 0) return;
      drag = {{ x: e.clientX, y: e.clientY, l: view.scrollLeft, t: view.scrollTop }};
      view.classList.add("dragging");
      view.setPointerCapture(e.pointerId);
    }});
    view.addEventListener("pointermove", e => {{
      if (!drag) return;
      view.scrollLeft = drag.l - (e.clientX - drag.x);
      view.scrollTop = drag.t - (e.clientY - drag.y);
    }});
    const end = () => {{ drag = null; view.classList.remove("dragging"); }};
    view.addEventListener("pointerup", end);
    view.addEventListener("pointercancel", end);
  }});
  sides.forEach(load);
}})();
</script>
"""


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--before', required=True)
    ap.add_argument('--after', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--before-label', default='Before')
    ap.add_argument('--after-label', default='After')
    ap.add_argument('--title', default='Residual Graphs')
    ap.add_argument('--about', default='Two runs’ residual graphs.')
    args = ap.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    graphs = {side: last_graph(getattr(args, side)) for side in ('before', 'after')}
    for side, dot in graphs.items():
        render(dot, out / f'{side}.svg')
    table = '\n'.join(
        f'        <tr><td>{html.escape(name)}</td><td>{b}</td><td>{a}</td></tr>'
        for name, b, a in rows(counts(graphs['before']), counts(graphs['after'])))
    (out / 'index.html').write_text(PAGE.format(
        title=html.escape(args.title), about=html.escape(args.about),
        before_label=html.escape(args.before_label), after_label=html.escape(args.after_label), rows=table))
    print(out / 'index.html')


if __name__ == '__main__':
    main()
