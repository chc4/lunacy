-- What the uxn_* benchmarks share: running a ROM on the Lua Varvara emulator
-- (varvara.lua) as they check it.

local varvara = require("varvara")

local M = {}

-- A fixed time for the datetime device, so a ROM reading it runs the same on
-- every Lua.
local CLOCK = { year = 2024, month = 3, day = 18, hour = 12, min = 0, sec = 0, wday = 2, yday = 78, isdst = false }
local function clock() return CLOCK end

-- A Varvara machine running `rom`, and its console's standard output and
-- standard error so far, each a function returning it as a string.
function M.machine(rom)
  local out = { {}, {} }
  local emu = varvara.new(rom, function(stream, byte)
    local buffer = out[stream]
    buffer[#buffer + 1] = string.char(byte)
  end, clock)
  return emu, function() return table.concat(out[1]) end, function() return table.concat(out[2]) end
end

-- How many of the screen's pixels have each palette index, 0 to 3 (the
-- foreground's where it isn't 0, else the background's), as "n0 n1 n2 n3".
function M.histogram(emu)
  local width, height, fg, bg = emu.screen()
  local counts = { [0] = 0, 0, 0, 0 }
  for i = 0, width * height - 1 do
    local c = fg[i]
    if c == 0 then c = bg[i] end
    counts[c] = counts[c] + 1
  end
  return string.format("%d %d %d %d", counts[0], counts[1], counts[2], counts[3])
end

-- Fails the benchmark with what it got if `got` isn't `expected`.
function M.check(what, got, expected)
  if got ~= expected then
    error(string.format("%s: got %q, expected %q", what, got, expected))
  end
end

return M
