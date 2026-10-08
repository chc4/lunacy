-- The ROM `rom` run headless on the Lua Varvara emulator: its reset vector,
-- its console's standard output to standard output.

local varvara = require("varvara")

local emu = varvara.new(require("rom"), function(stream, byte)
  if stream == 1 then io.write(string.char(byte)) end
end)
emu.boot(false)
