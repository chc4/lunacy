-- varvara/roms/loop_long.tal on the Lua Varvara emulator: its dispatch loop's
-- steady state. See varvara/uxn_bench.lua.
local bench = require("uxn_bench")
function run_iter(n) bench.run("loop", n, false) end
