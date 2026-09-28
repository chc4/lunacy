#!/usr/bin/env python3
"""Where a profile's time goes, by tier: from each profile recorded with call
graphs through frame pointers (as `just flamegraph` records them), the share of
samples in

  jit          JIT code (`jit_block_*`, named by the `perf` feature's map), or
               anything it called: helpers, natives, window ops it calls
  jit (unnamed) a sample in code with no symbol, with no JIT block under it:
               JIT code the map doesn't name (its entry and exit)
  interpreter  the specializer running residuals (`Specializer::run`), and
               anything it called, but for the tiers below
  specialize   the specializer compiling blocks: its generators, versions,
               subblocks and thunks
  jit compile  compiling blocks to machine code (`Specializer::jit_compile`)
  gc           the collector
  other        anything else: startup, loading the chunk, teardown

A sample goes to the first of gc, jit compile, specialize, jit, interpreter
whose frames are in its call chain, so compiling or collecting from JIT code
counts as compiling or collecting. A sample in the kernel goes to the tier of
the user code that entered it; `kernel` is the share of samples in the kernel,
across the tiers.

Frame pointers name a sample's callers but for the innermost: a sample on a
function's `ret`, after it restored its caller's frame pointer, has its caller
dropped from its chain. When the caller is JIT code, the sample goes to the
tier below it (the interpreter, which entered the JIT code); the `ret` of a
function JIT code calls often (e.g. `Tc::set` on an append) can move a
noticeable share. `perf script -F ip,sym` shows where a tier's samples are.

    tools/tiers.py perf-a.data [perf-b.data ...]

(`perf` must be on PATH, as in `nix develop`.)
"""
import re
import subprocess
import sys
from collections import Counter

TIERS = ['jit', 'jit (unnamed)', 'interpreter', 'specialize', 'jit compile', 'gc', 'other']
GC = re.compile(r'lunacy::gc::')
JIT_COMPILE = re.compile(r'Specializer>::jit_compile\b')
SPECIALIZE = re.compile(
    r'Specializer>::(compile|compile_one|subblock|version|block|new_block|make_\w+)\b'
    # A generator's own body (it runs while compiling); a residual it made is a
    # closure inside it, `emit_*::{closure#0}::{closure#N}`, which runs later.
    r'|lunacy::generators::emit_\w+::\{closure#0\}(\s|$)')
JIT = re.compile(r'\bjit_block_\d+')
INTERPRETER = re.compile(r'Specializer>::run\b')


# The kernel's half of the address space.
KERNEL = 1 << 63


def samples(path):
    """Each sample's frames, leaf first, as `perf script` prints them: (ip,
    symbol) pairs."""
    out = subprocess.run(['perf', 'script', '-i', path, '-F', 'ip,sym'],
                         capture_output=True, text=True, check=True).stdout
    frames = []
    for line in out.splitlines():
        line = line.strip()
        if not line:
            if frames:
                yield frames
            frames = []
            continue
        # `ip symbol`; the symbol may be absent.
        parts = line.split(None, 1)
        frames.append((int(parts[0], 16), parts[1] if len(parts) > 1 else '[unknown]'))
    if frames:
        yield frames


def tier(frames):
    """The sample's tier, by its user-space frames."""
    user = [sym for ip, sym in frames if ip < KERNEL]
    if not user:
        return 'other'
    for name, pattern in (('gc', GC), ('jit compile', JIT_COMPILE), ('specialize', SPECIALIZE), ('jit', JIT)):
        if any(pattern.search(f) for f in user):
            return name
    if user[0].startswith('[unknown]'):
        return 'jit (unnamed)'
    if any(INTERPRETER.search(f) for f in user):
        return 'interpreter'
    return 'other'


def main():
    if len(sys.argv) < 2:
        sys.exit(__doc__)
    width = max(len(p) for p in sys.argv[1:])
    print(f"{'profile':<{width}}  {'samples':>7}  " + '  '.join(f'{t:>13}' for t in TIERS + ['kernel']))
    for path in sys.argv[1:]:
        counts, kernel = Counter(), 0
        for frames in samples(path):
            counts[tier(frames)] += 1
            kernel += frames[0][0] >= KERNEL
        total = sum(counts.values())
        row = '  '.join(f'{100 * n / total:>12.1f}%' for n in [counts[t] for t in TIERS] + [kernel])
        print(f'{path:<{width}}  {total:>7}  {row}', flush=True)


if __name__ == '__main__':
    main()
