#!/usr/bin/env python3
"""A benchmark as one Lua file, for a Lua to compile or run: benchmarks/prelude.lua,
then each module the benchmark requires that is a file (its own directory's, then
varvara/'s, then lua_benchmarking/lualibs'), then the benchmark. With `--entry`,
any Lua program, in place of a benchmark.

A module `roms.<name>` is a Uxn ROM, a string: varvara/roms/<name>.tal, assembled
by `uxnasm` into working/roms/<name>.rom. With `--rom <name>`, the module `rom`
is that ROM.

A bundled module is loaded by a `require` the bundle defines, as Lua's own loads a
file: once, its result cached. Any other name goes to the Lua's `require`, but for
LuaJIT's `table.new` and `table.clear`, which a Lua other than LuaJIT gets as its
own `table` functions of those names if it has them, else plain Lua versions.

    bundle_bench.py <benchmark> > out.lua
    bundle_bench.py --entry varvara/snapshot.lua --rom screen > out.lua
"""
import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
REQUIRE = re.compile(r"""\brequire\s*\(?\s*["']([\w.]+)["']""")

# A Lua's `table` library may be read-only (Luau's): a function added to it goes
# in a copy, which the global `table` becomes.
def table_module(name, fallback):
    return (f'if jit then local m = __require("table.{name}") return m end\n'
            f"if not table.{name} then\n"
            "  local copy = {}\n"
            "  for k, v in pairs(table) do copy[k] = v end\n"
            f"  copy.{name} = {fallback}\n"
            "  table = copy\n"
            "end\n"
            f"return table.{name}")


TABLE_MODULES = {
    "table.new": table_module("new", "function() return {} end"),
    "table.clear": table_module("clear", "function(t) for k in pairs(t) do t[k] = nil end end"),
}


def bench_dir(name):
    for base in (ROOT / "benchmarks", ROOT / "lua_benchmarking" / "benchmarks"):
        if (base / name / "bench.lua").is_file():
            return base / name
    sys.exit(f"bundle_bench: no benchmark {name}")


def rom_module(name):
    """`return` of ROM `name`'s bytes, each a decimal escape, which every Lua reads."""
    tal = ROOT / "varvara" / "roms" / f"{name}.tal"
    if not tal.is_file():
        sys.exit(f"bundle_bench: no ROM {name}")
    rom = ROOT / "working" / "roms" / f"{name}.rom"
    rom.parent.mkdir(parents=True, exist_ok=True)
    assembled = subprocess.run(["uxnasm", str(tal), str(rom)], capture_output=True, text=True)
    if assembled.returncode != 0:
        sys.exit(f"bundle_bench: uxnasm failed on {tal}:\n{assembled.stdout}{assembled.stderr}")
    return 'return "' + "".join(f"\\{b:03d}" for b in rom.read_bytes()) + '"'


def module_file(name, dirs):
    rel = name.replace(".", "/") + ".lua"
    for d in dirs:
        if (d / rel).is_file():
            return d / rel
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("benchmark", nargs="?")
    parser.add_argument("--entry", type=Path, help="a Lua program to bundle, in place of a benchmark")
    parser.add_argument("--rom", help="the ROM the module `rom` is")
    args = parser.parse_args()
    if (args.benchmark is None) == (args.entry is None):
        parser.error("give a benchmark or --entry, not both")

    if args.entry is not None:
        here, main_path = args.entry.resolve().parent, args.entry
    else:
        here = bench_dir(args.benchmark)
        main_path = here / "bench.lua"
    dirs = [here, ROOT / "varvara", ROOT / "lua_benchmarking" / "lualibs"]
    main_src = main_path.read_text(encoding="latin-1")

    # Every module the benchmark reaches, depth first, each once.
    modules = dict(TABLE_MODULES)
    if args.rom is not None:
        modules["rom"] = rom_module(args.rom)
    pending = REQUIRE.findall(main_src)
    while pending:
        name = pending.pop()
        if name in modules:
            continue
        if name.startswith("roms."):
            modules[name] = rom_module(name.removeprefix("roms."))
            continue
        path = module_file(name, dirs)
        if path is None:
            continue
        src = path.read_text(encoding="latin-1")
        modules[name] = src
        pending.extend(REQUIRE.findall(src))

    out = [(ROOT / "benchmarks" / "prelude.lua").read_text(encoding="latin-1")]
    out.append(
        "local __require, __loaded, __loaders = require, {}, {}\n"
        "local function require(name)\n"
        "  local m = __loaded[name]\n"
        "  if m == nil then\n"
        "    local loader = __loaders[name]\n"
        "    if loader then m = loader() else m = __require(name) end\n"
        "    if m == nil then m = true end\n"
        "    __loaded[name] = m\n"
        "  end\n"
        "  return m\n"
        "end\n"
    )
    for name, src in modules.items():
        out.append(f"__loaders[{name!r}] = function()\n{src}\nend\n")
    out.append(main_src)
    # Sources are bytes, not always UTF-8: latin-1 passes each through.
    sys.stdout.buffer.write("\n".join(out).encode("latin-1"))


if __name__ == "__main__":
    main()
