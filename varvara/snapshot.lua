-- The screen of the ROM `rom` after Raven's snapshot test's input
-- (raven-varvara/tests/snapshots.rs): its reset vector, the mouse moved to the
-- screen's middle with its first button down, the right button pressed, `a`
-- typed, and 60 frames. Written to standard output as a binary PPM image; the
-- ROM's console output is dropped.

local varvara = require("varvara")

local emu = varvara.new(require("rom"), function() end)
emu.boot(false)
local width, height = emu.screen()
emu.mouse(math.floor(width / 2), math.floor(height / 2), 1)
emu.pressed("right")
emu.char(string.byte("a"))
for _ = 1, 60 do emu.frame() end

local fg, bg
width, height, fg, bg = emu.screen()
local palette = emu.palette
local rgb = {}
for c = 0, 3 do
  rgb[c] = string.char(palette[3 * c + 1], palette[3 * c + 2], palette[3 * c + 3])
end
io.write("P6\n", width, " ", height, "\n255\n")
for y = 0, height - 1 do
  local row = {}
  for x = 0, width - 1 do
    local i = y * width + x
    local c = fg[i]
    if c == 0 then c = bg[i] end
    row[x + 1] = rgb[c]
  end
  io.write(table.concat(row))
end
