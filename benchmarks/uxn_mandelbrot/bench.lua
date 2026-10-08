-- Uxntal's Mandelbrot set example (varvara/roms/mandelbrot.tal) on the Lua
-- Varvara emulator: the set in fixed point, a pixel at a time, on the screen.
-- Arithmetic on shorts, and the screen device's pixel port.

local bench = require("uxn_bench")
local ROM = require("roms.mandelbrot")

function run_iter(n)
  for _ = 1, n do
    local emu = bench.machine(ROM)
    emu.boot(false)
    bench.check("mandelbrot.tal's screen", bench.histogram(emu), "58933 38765 8062 3104")
  end
end
