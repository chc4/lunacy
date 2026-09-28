#!/usr/bin/env python3
"""A benchmark as one Lua file, for a Lua to compile or run: benchmarks/prelude.lua,
then each module the benchmark requires that is a file (its own directory's, then
lua_benchmarking/lualibs'), then the benchmark.

A bundled module is loaded by a `require` the bundle defines, as Lua's own loads a
file: once, its result cached. Any other name goes to the Lua's `require`, but for
LuaJIT's `table.new` and `table.clear`, which a Lua other than LuaJIT gets as its
own `table` functions of those names if it has them, else plain Lua versions.

    bundle_bench.py <benchmark> > out.lua
"""
import argparse
import re
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


def module_file(name, dirs):
    rel = name.replace(".", "/") + ".lua"
    for d in dirs:
        if (d / rel).is_file():
            return d / rel
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("benchmark")
    args = parser.parse_args()

    here = bench_dir(args.benchmark)
    dirs = [here, ROOT / "lua_benchmarking" / "lualibs"]
    main_src = (here / "bench.lua").read_text(encoding="latin-1")

    # Every module the benchmark reaches, depth first, each once.
    modules = dict(TABLE_MODULES)
    pending = REQUIRE.findall(main_src)
    while pending:
        name = pending.pop()
        if name in modules:
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
