-- varvara/roms/tak.tal on the Lua Varvara emulator, computing with the bit
-- library. See varvara/uxn_bench.lua.
local bench = require("uxn_bench")
function run_iter(n) bench.run("tak", n, true) end
