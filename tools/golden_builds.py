#!/usr/bin/env python3
"""Run golden tests (lua_tests/*.lua) under several builds of lunacy, each
test's output against its `-- EXPECT:` lines: the default release build,
`immediate_jit` (every block JIT compiled on first run), `no_dynamic_guards`
(every dynamic guard failing statically) and both. Each build is in
target/golden-<name>; a test that panics says where.

    tools/golden_builds.py lua_tests/a.lua [lua_tests/b.lua ...]

(in the devshell, which has luac5.1; `just golden-builds` runs it)
"""
import os
import subprocess
import sys
import tempfile

BUILDS = {
    'default': [],
    'immediate_jit': ['immediate_jit'],
    'no_dynamic_guards': ['no_dynamic_guards'],
    'immediate_jit+no_dynamic_guards': ['immediate_jit', 'no_dynamic_guards'],
}


def expected(test):
    return [line[len('-- EXPECT: '):] for line in open(test).read().splitlines() if line.startswith('-- EXPECT: ')]


def main():
    tests = sys.argv[1:]
    if not tests:
        sys.exit(__doc__)
    failed = 0
    with tempfile.TemporaryDirectory() as tmp:
        for name, features in BUILDS.items():
            target = os.path.abspath(f'target/golden-{name}')
            subprocess.run(['cargo', 'build', '--release', '--features', ' '.join(features), '--bin', 'lunacy', '--target-dir', target],
                           check=True, capture_output=True)
            for test in tests:
                binary = os.path.join(tmp, os.path.basename(test) + '.bin')
                subprocess.run(['luac5.1', '-o', binary, test], check=True)
                # In the temporary directory, where a build dumping files leaves them.
                run = subprocess.run([f'{target}/release/lunacy', binary], capture_output=True, text=True, cwd=tmp, timeout=600)
                got = [line for line in run.stdout.splitlines() if not line.startswith('counters after run')]
                want = expected(test)
                if run.returncode == 0 and got == want:
                    print(f'{name:32} {test}: ok')
                    continue
                failed += 1
                panic = next((line for line in run.stderr.splitlines() if 'panicked' in line), '')
                message = run.stderr.splitlines()[run.stderr.splitlines().index(panic) + 1] if panic else ''
                print(f'{name:32} {test}: FAILED (exit {run.returncode}) {panic} {message}')
                for index, (g, w) in enumerate(zip(got, want)):
                    if g != w:
                        print(f'    line {index + 1}: got {g!r}, want {w!r}')
                if len(got) != len(want):
                    print(f'    {len(got)} lines, want {len(want)}')
    return 1 if failed else 0


if __name__ == '__main__':
    sys.exit(main())
