-- The Varvara emulator (varvara.lua) in a window, through the `ui` library of
-- the `varvara` bin (src/bin/varvara.rs): the ROM in the global `rom` on its
-- screen, its controller driven by the keyboard and its mouse by the mouse over
-- the screen, with a panel of its console's output and one of its state, to
-- pause, step and reset it.

local varvara = require("varvara")

local BUTTONS = { "ctrl", "alt", "shift", "home", "up", "down", "left", "right" }
-- The console lines kept.
local CONSOLE_LINES = 24

-- The console's output: its finished lines, and the line being written.
local lines, line = {}, {}
local function write(_, byte)
  if byte == 10 then
    lines[#lines + 1] = table.concat(line)
    if #lines > CONSOLE_LINES then table.remove(lines, 1) end
    line = {}
  else
    line[#line + 1] = string.char(byte)
  end
end

local emu, frames
local function reset()
  lines, line = {}, {}
  emu = varvara.new(rom, write)
  emu.boot(false)
  frames = 0
end
reset()

local win = ui.open("Varvara", 1420, 720)
local width, height = emu.screen()
local screen = win:texture(width, height)

-- A stack's bytes, the top last.
local function stack(s, depth)
  local bytes = {}
  local p = s[257]
  for k = depth - 1, 0, -1 do
    bytes[#bytes + 1] = string.format("%02x", s[(p - k) % 256 + 1])
  end
  return table.concat(bytes, " ")
end

local held = {}
local paused, step, scale = false, false, 2
while win:frame() do
  for i = 1, #BUTTONS do
    local name = BUTTONS[i]
    local down = win:key(name)
    if down ~= (held[name] or false) then
      if down then emu.pressed(name) else emu.released(name) end
      held[name] = down
    end
  end
  local typed = win:typed()
  for i = 1, #typed do emu.char(typed:byte(i)) end
  local x, y = screen:pointer()
  if x >= 0 and y >= 0 and x < width and y < height then
    local buttons, wheel = win:mouse()
    emu.mouse(x, y, buttons, 0, -math.floor(wheel + 0.5))
  end

  if not paused or step then
    emu.frame()
    frames = frames + 1
    step = false
  end
  local fg, bg
  width, height, fg, bg = emu.screen()
  screen:update(width, height, fg, bg, emu.palette)

  if win:begin("Screen", 10, 10, width * scale + 20, height * scale + 40) then
    screen:image(scale)
  end
  win:finish()

  if win:begin("Machine", width * scale + 40, 10, 330, 300) then
    paused = win:checkbox("Paused", paused)
    win:same_line()
    if win:button("Step") then step = true end
    win:same_line()
    if win:button("Reset") then reset() end
    scale = win:slider("Scale", scale, 1, 4)
    win:separator()
    win:text(string.format("%dx%d, frame %d", width, height, frames))
    if emu.halted() then win:text(string.format("halted, exit code %d", emu.exit_code())) end
    win:text("WST " .. stack(emu.vm.wst, 8))
    win:text("RST " .. stack(emu.vm.rst, 8))
  end
  win:finish()

  if win:begin("Console", width * scale + 40, 320, 330, 300) then
    for i = 1, #lines do win:text(lines[i]) end
    if #line > 0 then win:text(table.concat(line)) end
  end
  win:finish()
end
