#!/usr/bin/env python3
"""The blocks a residual graph (`func_<line>.dot`, feature `graph`) reaches
from each block holding a residual matching `PATTERN`: each block's label (its
id, times entered, and residuals) and its edges, depth first, each block once,
to `DEPTH` edges deep. `just graph-golden` dumps a golden test's graphs.

    tools/graph_follow.py DOT PATTERN [DEPTH]
"""
import re
import sys

# A block's node line, and an edge, to a block or a native's call target.
NODE = re.compile(r'^\s*(\d+)\[id=\d+,shape=record,label="(.*?)"\]$', re.M)
EDGE = re.compile(r'^\s*(\d+) -> "?([0-9a-fx]+)"?(?: \[label=(\w+)\])?', re.M)


def main():
    text = open(sys.argv[1]).read()
    pattern = re.compile(sys.argv[2])
    depth_limit = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    blocks = {m.group(1): m.group(2) for m in NODE.finditer(text)}
    edges = {}
    for m in EDGE.finditer(text):
        edges.setdefault(m.group(1), []).append((m.group(2), m.group(3) or ''))
    seen = set()

    def show(block, depth):
        if block in seen or depth > depth_limit:
            return
        seen.add(block)
        print('  ' * depth + f'[{block}] {blocks[block]}')
        for target, label in edges.get(block, []):
            if target in blocks:
                print('  ' * depth + f'  -{label}-> {target}')
                show(target, depth + 1)

    for block, label in blocks.items():
        if pattern.search(label) and block not in seen:
            show(block, 0)
            print('----')


main()
