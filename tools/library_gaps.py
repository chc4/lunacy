#!/usr/bin/env python3
"""The library names a Lua program uses that lunacy's library lacks: each global it reads but
neither the library nor the program defines, and each member of a library table (`string.rep`) it
reads off that table that the table lacks and the program doesn't store itself. The program's uses
come from `luac5.1 -l -l`'s listing: a GETGLOBAL into a register, then a GETTABLE or SELF of that
register by a constant string, is a member read. A read the program never makes, as the right of
an `or` whose left is true, is listed too. Lunacy's names come from running
tools/library_probe.lua under it.

    tools/library_gaps.py LUNACY_BINARY FILE.lua...
"""
import os
import re
import subprocess
import sys
import tempfile

GETGLOBAL = re.compile(r'\bGETGLOBAL\s+(\d+)\s+-?\d+\s+; (\S+)')
SETGLOBAL = re.compile(r'\bSETGLOBAL\s+\d+\s+-?\d+\s+; (\S+)')
INDEXED = re.compile(r'\b(?:GETTABLE|SELF)\s+\d+\s+(\d+)\s+-?\d+\s+; "([^"]*)"')
STORED = re.compile(r'\bSETTABLE\s+(\d+)\s+-?\d+\s+-?\d+\s+; "([^"]*)"')
# An instruction writing register A, which ends what an earlier GETGLOBAL into it named.
WRITES = re.compile(r'^\s*\d+\s+\[\d+\]\s+([A-Z]+)\s+(\d+)')
FUNCTION = re.compile(r'^(main|function) <')


def library(lunacy):
    """The names lunacy's library has, as the probe prints them."""
    probe = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'library_probe.lua')
    with tempfile.TemporaryDirectory() as tmp:
        binary = os.path.join(tmp, 'probe.bin')
        subprocess.run(['luac5.1', '-o', binary, probe], check=True)
        out = subprocess.run([lunacy, binary], capture_output=True, text=True, check=True).stdout
    return {line.strip() for line in out.splitlines() if line.strip() and not line.startswith('counters')}


def uses(path):
    """The globals `path` reads, the members of globals it reads off them, and the globals and
    members it sets."""
    listing = subprocess.run(['luac5.1', '-l', '-l', '-p', path], capture_output=True, text=True, check=True).stdout
    read, members, defined = set(), set(), set()
    named = {}
    for line in listing.splitlines():
        if FUNCTION.match(line):
            named = {}
            continue
        if m := SETGLOBAL.search(line):
            defined.add(m.group(1))
        if (m := STORED.search(line)) and m.group(1) in named:
            defined.add(f'{named[m.group(1)]}.{m.group(2)}')
        if m := INDEXED.search(line):
            if m.group(1) in named:
                members.add(f'{named[m.group(1)]}.{m.group(2)}')
        if m := GETGLOBAL.search(line):
            read.add(m.group(2))
            named[m.group(1)] = m.group(2)
        elif m := WRITES.match(line):
            named.pop(m.group(2), None)
    return read, members, defined


def main():
    lunacy, paths = sys.argv[1], sys.argv[2:]
    have = library(lunacy)
    for path in paths:
        read, members, defined = uses(path)
        missing = sorted(name for name in read if name not in have and name not in defined)
        missing += sorted(m for m in members if m.split('.')[0] in have and m not in have and m not in defined)
        print(f'{os.path.basename(path)}: {" ".join(missing) if missing else "nothing missing"}')


if __name__ == '__main__':
    main()
