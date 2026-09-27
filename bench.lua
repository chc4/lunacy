-- Run a compiled benchmark: `lua bench.lua -- <benchmark>.bin <times>`, the
-- benchmark's bytecode (luac5.1's for lua5.1, luac5.5's for lua5.5, `luajit
-- -b`'s for LuaJIT), as lunacy runs it. It defines `run_iter`.
local args = {...}

dofile(args[2])

run_iter(tonumber(args[3]))
