#!/usr/bin/env python3
"""Each variant of an enum of src/*.rs and how often src names it elsewhere than its declaration:
a variant named once is never made nor matched, and one named only where it is matched is never
made. A candidate list to check by hand: a variant made through a macro, or a `use` of the enum's
variants, isn't counted.

    tools/unused_variants.py Enum [Enum...]
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def main(enums):
    sources = {path: path.read_text() for path in sorted((ROOT / 'src').glob('*.rs'))}
    text = '\n'.join(sources.values())
    for enum in enums:
        for source in sources.values():
            match = re.search(r'^pub(?:\([a-z]+\))? enum ' + enum + r'\b[^{]*\{\n(.*?)^\}', source, re.S | re.M)
            if match:
                break
        else:
            sys.exit(f'no enum {enum}')
        for variant in re.findall(r'^    ([A-Z][A-Za-z0-9]*)', match.group(1), re.M):
            uses = len(re.findall(r'\b' + enum + r'::' + variant + r'\b', text))
            print(f'{enum}::{variant} {uses}')


if __name__ == '__main__':
    main(sys.argv[1:])
