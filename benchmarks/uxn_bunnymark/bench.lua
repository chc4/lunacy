-- Uxntal's bunnymark (varvara/roms/bunnymark.tal) on the Lua Varvara emulator:
-- 300 frames with the mouse's button held, which adds a bunny each frame, every
-- frame clearing the screen and drawing each bunny's sprite where it bounces
-- to. The screen device's fill and sprites.

local bench = require("uxn_bench")
local ROM = require("roms.bunnymark")

local FRAMES = 300

function run_iter(n)
  for _ = 1, n do
    local emu = bench.machine(ROM)
    emu.boot(false)
    emu.mouse(0, 0, 1)
    for _ = 1, FRAMES do emu.frame() end
    bench.check("bunnymark.tal's screen", bench.histogram(emu), "140277 6083 14331 3149")
  end
end
