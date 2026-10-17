#!/usr/bin/env python3
"""A table of `just hyperfines-knob`, `just hyperfines-knobs` or `just
hyperfines-feature` runs: per benchmark, the median time of each command, and
each one's change against the first's, then the geometric mean of each one's
changes.

    tools/knob_table.py working/knob/*.json
"""
import json
import math
import sys
from pathlib import Path

import hyperfine_json


def main(paths):
    rows, names = [], None
    for path in paths:
        # A run that failed left no results.
        text = Path(path).read_text()
        if not text.strip():
            continue
        results = hyperfine_json.results(text, text=True)
        if len(results) < 2 or (names is not None and len(results) != len(names)):
            continue
        names = names or [r['command'] for r in results]
        rows.append((Path(path).stem, [r['median'] for r in results]))
    if not rows:
        sys.exit('no runs')
    for i, name in enumerate(names):
        print(f'{i}: {name}')
    print(f'{"benchmark":<24}' + ''.join(f'{i:>9}' for i in range(len(names))) + ''.join(f'{f"{i} vs 0":>10}' for i in range(1, len(names))))
    for name, medians in rows:
        print(f'{name:<24}' + ''.join(f'{m:9.4f}' for m in medians)
              + ''.join(f'{100 * (m / medians[0] - 1):+9.1f}%' for m in medians[1:]))
    for i in range(1, len(names)):
        mean = math.exp(sum(math.log(medians[i] / medians[0]) for _, medians in rows) / len(rows))
        print(f'geometric mean of {len(rows)}, {names[i]} against {names[0]}: {100 * (mean - 1):+.2f}%')


if __name__ == '__main__':
    main(sys.argv[1:])
