-- The uxn_* benchmarks: Uxntal programs (varvara/roms) on the Lua Varvara
-- emulator (varvara.lua), each checking what its program does. `run(name, n,
-- bitwise)` runs program `name` `n` times, each on a new machine, which is
-- `bitwise` for the uxn_bit_* benchmarks (see `varvara.new`).

local varvara = require("varvara")

local M = {}

-- A fixed time for the datetime device, so a ROM reading it runs the same on
-- every Lua.
local CLOCK = { year = 2024, month = 3, day = 18, hour = 12, min = 0, sec = 0, wday = 2, yday = 78, isdst = false }
local function clock() return CLOCK end

-- A Varvara machine running `rom`, and its console's standard output and
-- standard error so far, each a function returning it as a string.
local function machine(rom, bitwise)
  local out = { {}, {} }
  local emu = varvara.new(rom, function(stream, byte)
    local buffer = out[stream]
    buffer[#buffer + 1] = string.char(byte)
  end, clock, bitwise)
  return emu, function() return table.concat(out[1]) end, function() return table.concat(out[2]) end
end

-- How many of the screen's pixels have each palette index, 0 to 3 (the
-- foreground's where it isn't 0, else the background's), as "n0 n1 n2 n3".
local function histogram(emu)
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
local function check(what, got, expected)
  if got ~= expected then
    error(string.format("%s: got %q, expected %q", what, got, expected))
  end
end

local FIB_OUTPUT
do
  local lines, a, b = {}, 1, 1
  for i = 1, 24 do
    lines[i] = string.format("%d %d %d\n", i, a, a)
    a, b = b, a + b
  end
  FIB_OUTPUT = table.concat(lines)
end

-- Each program, run once on a new machine.
local PROGRAMS = {
  -- fib.tal: for 1 to 24, the number, its Fibonacci number by recursion and by
  -- tail recursion, printed in decimal on the console. Calls and the return
  -- stack.
  fib = function(bitwise)
    local emu, stdout = machine(require("roms.fib"), bitwise)
    emu.boot(false)
    check("fib.tal's output", stdout(), FIB_OUTPUT)
  end,
  -- tak.tal: tak(24, 20, 11) in bytes, which prints its stacks, the result on
  -- top of the working stack. Deep recursion through the return stack.
  tak = function(bitwise)
    local emu, _, stderr = machine(require("roms.tak"), bitwise)
    emu.boot(false)
    check("tak.tal's stacks", stderr(), "WST 00 00 00 00 00 00 00|0c < \nRST 00 00 00 00 00 00 00 00|< \n")
  end,
  -- mandelbrot.tal: the set in fixed point, a pixel at a time, on the screen.
  -- Arithmetic on shorts, and the screen device's pixel port.
  mandelbrot = function(bitwise)
    local emu = machine(require("roms.mandelbrot"), bitwise)
    emu.boot(false)
    check("mandelbrot.tal's screen", histogram(emu), "58933 38765 8062 3104")
  end,
  -- loop_long.tal: a loop of nothing, a million times, which prints nothing:
  -- the emulator's dispatch and a few stack operations, in its steady state.
  loop = function(bitwise)
    local emu, stdout = machine(require("roms.loop_long"), bitwise)
    emu.boot(false)
    check("loop_long.tal's output", stdout(), "")
  end,
  -- loop_short.tal: loop_long.tal's loop run once, not 16 times, for the cost
  -- of one of its iterations from the two's difference.
  loop_short = function(bitwise)
    local emu, stdout = machine(require("roms.loop_short"), bitwise)
    emu.boot(false)
    check("loop_short.tal's output", stdout(), "")
  end,
  -- bunnymark.tal: 300 frames with the mouse's button held, which adds a bunny
  -- each frame, every frame clearing the screen and drawing each bunny's
  -- sprite where it bounces to. The screen device's fill and sprites.
  bunnymark = function(bitwise)
    local emu = machine(require("roms.bunnymark"), bitwise)
    emu.boot(false)
    emu.mouse(0, 0, 1)
    for _ = 1, 300 do emu.frame() end
    check("bunnymark.tal's screen", histogram(emu), "140277 6083 14331 3149")
  end,
}

function M.run(name, n, bitwise)
  local program = PROGRAMS[name]
  for _ = 1, n do program(bitwise) end
end

return M
