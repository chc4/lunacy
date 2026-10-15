#!/usr/bin/env python3
"""A table of `just hyperfines-knob` or `just hyperfines-feature` runs: per
benchmark, the median time without the knob or feature and with it, and the
change, then the geometric mean of the changes.

    tools/knob_table.py working/knob/*.json
"""
import json
import math
import sys
from pathlib import Path

import hyperfine_json


def main(paths):
    rows, ratios = [], []
    for path in paths:
        # A run that failed left no results.
        text = Path(path).read_text()
        if not text.strip():
            continue
        results = hyperfine_json.results(text, text=True)
        if len(results) != 2:
            continue
        base, knob = (r['median'] for r in results)
        rows.append((Path(path).stem, base, knob, results[1]['command']))
        ratios.append(knob / base)
    if not rows:
        sys.exit('no runs')
    print(f'{"benchmark":<24} {"default":>9} {"knob":>9} {"change":>8}')
    for name, base, knob, _ in rows:
        print(f'{name:<24} {base:9.4f} {knob:9.4f} {100 * (knob / base - 1):+7.1f}%')
    mean = math.exp(sum(math.log(r) for r in ratios) / len(ratios))
    print(f'geometric mean of {len(ratios)}: {100 * (mean - 1):+.2f}% with the knob')


if __name__ == '__main__':
    main(sys.argv[1:])
