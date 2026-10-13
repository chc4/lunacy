#!/usr/bin/env python3
"""Functions, methods, and types of src/*.rs whose name appears nowhere else in src:
candidates for deletion, as the crate allows dead code. A name shared with another
item, or reached only through a macro or a trait, is a false positive to check by
hand.

    tools/unused_fns.py [file...]
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ITEM = re.compile(r'^\s*(?:pub(?:\([a-z]+\))? )?(?:const )?(?:fn|struct|enum|type) ([A-Za-z_][A-Za-z0-9_]*)', re.M)


def main(files):
    sources = {path: path.read_text() for path in sorted((ROOT / 'src').glob('*.rs'))}
    text = '\n'.join(sources.values())
    counts = {}
    for name in re.findall(r'\b[A-Za-z_][A-Za-z0-9_]*\b', text):
        counts[name] = counts.get(name, 0) + 1
    wanted = [ROOT / f for f in files] if files else list(sources)
    for path in wanted:
        source = sources[path.resolve()]
        for match in ITEM.finditer(source):
            name = match.group(1)
            if counts.get(name, 0) <= 1 and name != 'main':
                line = source.count('\n', 0, match.start()) + 1
                print(f'{path.relative_to(ROOT)}:{line} {name}')


if __name__ == '__main__':
    main(sys.argv[1:])
