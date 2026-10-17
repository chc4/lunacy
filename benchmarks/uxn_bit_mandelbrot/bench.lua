-- varvara/roms/mandelbrot.tal on the Lua Varvara emulator, computing with the bit
-- library. See varvara/uxn_bench.lua.
local bench = require("uxn_bench")
function run_iter(n) bench.run("mandelbrot", n, true) end
