#!/usr/bin/env python3
"""Total profiles' cycles by what spent them: JIT code, hash key lookups' slow paths, the
specializer, the JIT compiler, the collector and allocator, the rest of the runtime, and the kernel.

Reads `perf report --no-children -g none --no-inline --sort dso,sym --stdio --percent-limit 0`
output, one file per profile (`just perf-components` makes them), and scales each symbol's
share by the profile's event count, so profiles of runs of different lengths compare. With two
profiles, the difference between them.

JIT code is the `[JIT]` mapping's samples, and `[unknown]` user samples what perf can't name: JIT
code too, mostly its stencils and helpers. Kernel samples are apart. A native symbol is a hash key
lookup's slow path if it is one an `HrefInit` site runs on a miss, the specializer's if it names the
specializer, its classes or its window allocator, the JIT compiler's if it names the JIT but its
helpers (which JIT code calls), and the collector's if it names the collector or mimalloc.
"""
import argparse
import re
from collections import defaultdict

EVENTS = re.compile(r'^# Event count \(approx\.\): (\d+)')
LINE = re.compile(r'^\s*([\d.]+)%\s+(?:\d+\s+)?(\[JIT\] tid \d+|\S+)\s+\[(.)\]\s+(.*?)\s*$')
COMPONENTS = ['JIT code', 'JIT stencils and helpers', 'hash key slow paths', 'specializer', 'JIT compiler', 'collector and allocator', 'runtime', 'kernel']


def component(dso, mode, sym):
    if mode == 'k':
        return 'kernel'
    if dso.startswith('[JIT]'):
        return 'JIT code'
    if dso == '[unknown]':
        return 'JIT stencils and helpers'
    if any(name in sym for name in ('href_init_slow', 'href_init_miss', 'HrefInitAt')):
        return 'hash key slow paths'
    if any(name in sym for name in ('specialize', 'Specializer', 'lunacy::classes', 'window_alloc')):
        return 'specializer'
    if 'lunacy::jit::' in sym and 'JitHelper' not in sym:
        return 'JIT compiler'
    if 'lunacy::gc' in sym or 'gc::Mark' in sym or sym.startswith(('mi_', '_mi_')):
        return 'collector and allocator'
    return 'runtime'


def totals(path):
    events, out = None, defaultdict(float)
    for line in open(path):
        if m := EVENTS.match(line):
            events = int(m.group(1))
        elif m := LINE.match(line):
            out[component(m.group(2), m.group(3), m.group(4))] += float(m.group(1))
    if events is None:
        raise SystemExit(f'{path}: no event count')
    return {name: share * events / 100 for name, share in out.items()}


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('reports', nargs='+', help='perf report outputs')
    args = ap.parse_args()
    profiles = [totals(path) for path in args.reports]
    names = [path.rsplit('/', 1)[-1][:14] for path in args.reports]
    header = f"{'component':26}" + ''.join(f'{name:>15}' for name in names)
    print(header + ('       change' if len(profiles) == 2 else ''))
    for name in COMPONENTS + ['total']:
        values = [sum(p.values()) if name == 'total' else p.get(name, 0) for p in profiles]
        row = f'{name:26}' + ''.join(f'{v / 1e6:13.0f} M' for v in values)
        if len(profiles) == 2:
            row += f'{(values[0] - values[1]) / 1e6:+11.0f} M'
        print(row)


if __name__ == '__main__':
    main()
