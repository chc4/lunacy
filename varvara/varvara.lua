-- The Varvara computer (https://wiki.xxiivv.com/site/varvara.html): a Uxn CPU
-- and its devices, as the reference emulator (uxnemu, uxncli) has them. Of its
-- devices this has the system, console, screen, controller, mouse and datetime;
-- a ROM writing to the audio or file devices' ports only sets them, as if the
-- device were absent.
--
-- `new(rom, write, clock, bitwise)` makes one with `rom`, a string, loaded:
-- `write(stream, byte)` takes its console output, stream 1 its standard output
-- and 2 its standard error, and `clock()` is the time its datetime device
-- reads, a table as `os.date("*t")` makes (by default `os.date`'s time, where
-- the Lua has it; without a clock, the datetime ports read as they were set).
-- A `bitwise` one computes with the bit library (`bit`, or Luau's `bit32`): its
-- CPU is uxn_bit.lua's, and its sprites and device flags are decoded by masks
-- and shifts. Either runs any ROM the same. The host
-- then runs it: `boot` runs its reset vector, then `frame` its screen vector 60
-- times a second, and the input functions their devices' vectors.

local uxn = require("uxn")

local floor = math.floor

local M = {}

-- A sprite pixel's color, by the pixel's two bits (the rows) and the sprite's
-- blending mode (the columns); and, per mode, whether its pixels of 0 are drawn.
local BLENDING = {
  [0] = { [0] = 0, 0, 0, 0, 1, 0, 1, 1, 2, 2, 0, 2, 3, 3, 3, 0 },
  { [0] = 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3 },
  { [0] = 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 3, 1 },
  { [0] = 2, 3, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2, 2, 3, 1, 2 },
}
local OPAQUE = { [0] = false, true, true, true, true, false, true, true, true, true, false, true, true, true, true, false }

-- The controller's buttons, by key name.
M.BUTTONS = { ctrl = 0x01, alt = 0x02, shift = 0x04, home = 0x08, up = 0x10, down = 0x20, left = 0x40, right = 0x80 }

-- The console's input types.
M.CONSOLE_STDIN, M.CONSOLE_ARG, M.CONSOLE_EOA, M.CONSOLE_END = 1, 2, 3, 4

-- Expansion memory's pages, the program's included.
local RAM_PAGES = 16

function M.new(rom, write, clock, bitwise)
  if clock == nil and os and os.date then
    clock = function() return os.date("*t") end
  end
  -- The bit library, for a machine that is `bitwise`.
  local bit = bitwise and (bit or bit32)
  local vm = (bitwise and require("uxn_bit") or uxn).new()

  -- Whether bit `mask` (a power of two) of byte `b` is set.
  local has
  if bitwise then
    local band = bit.band
    has = function(b, mask) return band(b, mask) ~= 0 end
  else
    has = function(b, mask) return b % (mask * 2) >= mask end
  end
  local ram, wst, rst = vm.ram, vm.wst, vm.rst
  local dev = {}
  for i = 0, 255 do dev[i] = 0 end
  local dei, deo = {}, {}

  local function write_string(stream, s)
    for i = 1, #s do write(stream, s:byte(i)) end
  end

  local function short(port)
    return dev[port] * 256 + dev[port + 1]
  end

  -- Runs the vector at `port`, unless it's unset or the machine has halted.
  local function vector(port)
    local addr = short(port)
    if addr ~= 0 and dev[0x0f] == 0 then vm:eval(addr) end
  end

  -- System

  -- Expansion memory's pages past the first, made when first used.
  local pages = { ram }
  local function page(n)
    n = n % RAM_PAGES
    local p = pages[n + 1]
    if not p then
      p = {}
      for i = 1, 65536 do p[i] = 0 end
      pages[n + 1] = p
    end
    return p
  end

  local function peek2(addr)
    return ram[addr % 65536 + 1] * 256 + ram[(addr + 1) % 65536 + 1]
  end

  -- System/expansion: a command in RAM, at the port's address, to fill or copy
  -- memory across pages.
  deo[0x03] = function()
    local addr = short(0x02)
    local command, length = ram[addr + 1], peek2(addr + 1)
    if command == 0 then
      local dst, at, value = page(peek2(addr + 3)), peek2(addr + 5), ram[(addr + 7) % 65536 + 1]
      for i = 0, length - 1 do dst[(at + i) % 65536 + 1] = value end
    elseif command == 1 or command == 2 then
      local src, from = page(peek2(addr + 3)), peek2(addr + 5)
      local dst, to = page(peek2(addr + 7)), peek2(addr + 9)
      local first, last, step = 0, length - 1, 1
      if command == 2 then first, last, step = length - 1, 0, -1 end
      for i = first, last, step do dst[(to + i) % 65536 + 1] = src[(from + i) % 65536 + 1] end
    else
      write_string(2, string.format("Unknown Expansion Command 0x%02x\n", command))
    end
  end
  dei[0x04] = function() return wst[257] end
  dei[0x05] = function() return rst[257] end
  deo[0x04] = function(v) wst[257] = v end
  deo[0x05] = function(v) rst[257] = v end

  -- The palette's four colors, each its red, green and blue, 0 to 255, at
  -- 3 * color + 1 to 3 * color + 3: from the system's color ports, a nibble
  -- for each color's red, green and blue.
  local palette = {}
  local function set_palette()
    for i = 0, 3 do
      local high = i % 2 == 0
      for c = 0, 2 do
        local byte = dev[0x08 + 2 * c + floor(i / 2)]
        local nibble = high and floor(byte / 16) or byte % 16
        palette[3 * i + c + 1] = nibble * 17
      end
    end
  end
  set_palette()
  for port = 0x08, 0x0d do deo[port] = set_palette end

  -- System/debug: the stacks' top bytes, to standard error.
  local function inspect(name, s)
    local line = { name }
    local p = s[257]
    for k = 7, 0, -1 do
      local i = (p - k) % 256
      line[#line + 1] = string.format("%02x%s", s[i + 1], i == 0 and "|" or " ")
    end
    line[#line + 1] = "< \n"
    write_string(2, table.concat(line))
  end
  deo[0x0e] = function()
    inspect("WST ", wst)
    inspect("RST ", rst)
  end

  -- Console

  deo[0x18] = function(v) write(1, v) end
  deo[0x19] = function(v) write(2, v) end

  -- Screen: two layers of 2-bit pixels, the foreground drawn over the
  -- background where it isn't 0, each a table from x + y * width.

  local width, height = 64 * 8, 40 * 8
  local fg, bg = {}, {}
  local function clear()
    fg, bg = {}, {}
    for i = 0, width * height - 1 do fg[i], bg[i] = 0, 0 end
  end
  clear()
  local function resize(w, h)
    if w < 8 or h < 8 or w >= 0x800 or h >= 0x800 then return end
    if w == width and h == height then return end
    width, height = w, h
    clear()
  end
  deo[0x23] = function() resize(short(0x22), height) end
  deo[0x25] = function() resize(width, short(0x24)) end
  dei[0x22] = function() return floor(width / 256) end
  dei[0x23] = function() return width % 256 end
  dei[0x24] = function() return floor(height / 256) end
  dei[0x25] = function() return height % 256 end

  -- The position and sprite address registers, and the auto byte's flags: to
  -- advance x and y after a pixel or sprite, to advance the address after a
  -- sprite, and how many more sprites a sprite draws.
  local x, y, addr = 0, 0, 0
  local auto_x, auto_y, auto_addr, auto_len = false, false, false, 0
  deo[0x26] = function(v)
    auto_x, auto_y, auto_addr, auto_len = has(v, 1), has(v, 2), has(v, 4), floor(v / 16)
  end
  deo[0x28] = function() x = short(0x28) end
  deo[0x29] = deo[0x28]
  deo[0x2a] = function() y = short(0x2a) end
  deo[0x2b] = deo[0x2a]
  deo[0x2c] = function() addr = short(0x2c) end
  deo[0x2d] = deo[0x2c]
  dei[0x28] = function() return floor(x / 256) end
  dei[0x29] = function() return x % 256 end
  dei[0x2a] = function() return floor(y / 256) end
  dei[0x2b] = function() return y % 256 end
  dei[0x2c] = function() return floor(addr / 256) end
  dei[0x2d] = function() return addr % 256 end

  -- Screen/pixel: a pixel at x, y, or the rectangle from it to an edge.
  deo[0x2e] = function(ctrl)
    local color = ctrl % 4
    local layer = has(ctrl, 0x40) and fg or bg
    if ctrl >= 0x80 then
      local x1, x2, y1, y2 = x, width, y, height
      if has(ctrl, 0x10) then x1, x2 = 0, x end
      if has(ctrl, 0x20) then y1, y2 = 0, y end
      if x2 > width then x2 = width end
      if y2 > height then y2 = height end
      for py = y1, y2 - 1 do
        local row = py * width
        for px = x1, x2 - 1 do layer[row + px] = color end
      end
    else
      if x < width and y < height then layer[x + y * width] = color end
      if auto_x then x = (x + 1) % 65536 end
      if auto_y then y = (y + 1) % 65536 end
    end
  end

  -- An 8x8 sprite from `at` in RAM, at x1, y1, its rows and columns in the
  -- order `fx` and `fy` (1, or -1 to flip), in 1 or 2 bits a pixel.
  local sprite
  if bitwise then
    local band, bor, lshift, rshift = bit.band, bit.bor, bit.lshift, bit.rshift
    sprite = function(layer, at, x1, y1, color, fx, fy, twobpp)
      local opaque = OPAQUE[color]
      for j = 0, 7 do
        local py = fy > 0 and band(y1 + j, 65535) or band(y1 + 7 - j, 65535)
        if py < height then
          local lo = ram[band(at + j, 65535) + 1]
          local hi = twobpp and ram[band(at + j + 8, 65535) + 1] or 0
          local row = py * width
          -- From the low bit, the sprite's rightmost pixel.
          for i = 0, 7 do
            local px = fx > 0 and band(x1 + 7 - i, 65535) or band(x1 + i, 65535)
            local ch = bor(band(rshift(lo, i), 1), lshift(band(rshift(hi, i), 1), 1))
            if px < width and (opaque or ch ~= 0) then layer[row + px] = BLENDING[ch][color] end
          end
        end
      end
    end
  else
    sprite = function(layer, at, x1, y1, color, fx, fy, twobpp)
      local opaque = OPAQUE[color]
      for j = 0, 7 do
        local py = fy > 0 and (y1 + j) % 65536 or (y1 + 7 - j) % 65536
        if py < height then
          local lo = ram[(at + j) % 65536 + 1]
          local hi = twobpp and ram[(at + j + 8) % 65536 + 1] or 0
          local row = py * width
          -- From the low bit, the sprite's rightmost pixel.
          for i = 0, 7 do
            local px = fx > 0 and (x1 + 7 - i) % 65536 or (x1 + i) % 65536
            local lo_bit, hi_bit = lo % 2, hi % 2
            local ch = lo_bit + 2 * hi_bit
            lo, hi = (lo - lo_bit) / 2, (hi - hi_bit) / 2
            if px < width and (opaque or ch ~= 0) then layer[row + px] = BLENDING[ch][color] end
          end
        end
      end
    end
  end

  -- Screen/sprite: auto's length more sprites past the first, each moved by
  -- auto y along x and by auto x along y, and from the next sprite's address
  -- with auto addr.
  deo[0x2f] = function(ctrl)
    local twobpp = ctrl >= 0x80
    local color = ctrl % 16
    local layer = has(ctrl, 0x40) and fg or bg
    local fx = has(ctrl, 0x10) and -1 or 1
    local fy = has(ctrl, 0x20) and -1 or 1
    local dx = auto_x and 8 or 0
    local dy = auto_y and 8 or 0
    local step = auto_addr and (twobpp and 16 or 8) or 0
    for i = 0, auto_len do
      sprite(layer, addr, (x + dy * fx * i) % 65536, (y + dx * fy * i) % 65536, color, fx, fy, twobpp)
      addr = (addr + step) % 65536
    end
    if auto_x then x = (x + dx * fx) % 65536 end
    if auto_y then y = (y + dy * fy) % 65536 end
  end

  -- Datetime, from `clock`.
  if clock then
    local function field(f) return function() return f(clock()) end end
    dei[0xc0] = field(function(t) return floor(t.year / 256) end)
    dei[0xc1] = field(function(t) return t.year % 256 end)
    dei[0xc2] = field(function(t) return t.month - 1 end)
    dei[0xc3] = field(function(t) return t.day end)
    dei[0xc4] = field(function(t) return t.hour end)
    dei[0xc5] = field(function(t) return t.min end)
    dei[0xc6] = field(function(t) return t.sec end)
    dei[0xc7] = field(function(t) return t.wday - 1 end)
    dei[0xc8] = field(function(t) return floor((t.yday - 1) / 256) end)
    dei[0xc9] = field(function(t) return (t.yday - 1) % 256 end)
    dei[0xca] = field(function(t) return t.isdst and 1 or 0 end)
  end

  vm:set_devices(function(port)
    local f = dei[port]
    if f then return f() end
    return dev[port]
  end, function(port, value)
    dev[port] = value
    local f = deo[port]
    if f then f(value) end
  end)

  vm:load(rom)

  local emu = { vm = vm, dev = dev, palette = palette }

  -- Runs the reset vector, with the console's type saying whether the ROM has
  -- arguments.
  function emu.boot(has_args)
    dev[0x17] = has_args and 1 or 0
    if dev[0x0f] == 0 then vm:eval(0x100) end
  end

  -- Whether the ROM has halted, and its exit code.
  function emu.halted() return dev[0x0f] ~= 0 end
  function emu.exit_code() return dev[0x0f] % 128 end

  function emu.frame() vector(0x20) end

  -- The screen's size and its layers.
  function emu.screen() return width, height, fg, bg end

  -- A byte of console input, of a type in `CONSOLE_*`.
  function emu.console(c, type)
    dev[0x12], dev[0x17] = c, type
    vector(0x10)
  end

  -- Controller: a button pressed or released, by its name in BUTTONS, or a key's
  -- character typed.
  function emu.pressed(name)
    local mask = M.BUTTONS[name]
    if not has(dev[0x82], mask) then
      dev[0x82] = dev[0x82] + mask
      vector(0x80)
    end
  end
  function emu.released(name)
    local mask = M.BUTTONS[name]
    if has(dev[0x82], mask) then
      dev[0x82] = dev[0x82] - mask
      vector(0x80)
    end
  end
  function emu.char(c)
    if c == 0 then return end
    dev[0x83] = c
    vector(0x80)
    dev[0x83] = 0
  end

  -- Mouse: its position, buttons (a bit each) and scroll this frame, which run
  -- its vector once if any changed.
  function emu.mouse(mx, my, buttons, scroll_x, scroll_y)
    local changed = false
    mx, my = mx % 65536, my % 65536
    if short(0x92) ~= mx or short(0x94) ~= my then
      dev[0x92], dev[0x93] = floor(mx / 256), mx % 256
      dev[0x94], dev[0x95] = floor(my / 256), my % 256
      changed = true
    end
    if dev[0x96] ~= buttons then
      dev[0x96] = buttons
      changed = true
    end
    local sx, sy = (scroll_x or 0) % 65536, (scroll_y or 0) % 65536
    if sx ~= 0 or sy ~= 0 then
      dev[0x9a], dev[0x9b] = floor(sx / 256), sx % 256
      dev[0x9c], dev[0x9d] = floor(sy / 256), sy % 256
      changed = true
    end
    if changed then vector(0x90) end
    dev[0x9a], dev[0x9b], dev[0x9c], dev[0x9d] = 0, 0, 0, 0
  end

  return emu
end

return M
