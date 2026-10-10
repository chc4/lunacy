-- varvara/roms/loop_short.tal on the Lua Varvara emulator: uxn_loop's loop run
-- once, not 16 times, for one iteration's cost from the two's difference. See
-- varvara/uxn_bench.lua.
local bench = require("uxn_bench")
function run_iter(n) bench.run("loop_short", n, false) end
