-- Uxntal's Fibonacci example (varvara/roms/fib.tal) on the Lua Varvara
-- emulator: for 1 to 24, the number, its Fibonacci number by recursion and by
-- tail recursion, printed in decimal on the console. Calls and the return stack.

local bench = require("uxn_bench")
local ROM = require("roms.fib")

local EXPECTED
do
  local lines, a, b = {}, 1, 1
  for i = 1, 24 do
    lines[i] = string.format("%d %d %d\n", i, a, a)
    a, b = b, a + b
  end
  EXPECTED = table.concat(lines)
end

function run_iter(n)
  for _ = 1, n do
    local emu, stdout = bench.machine(ROM)
    emu.boot(false)
    bench.check("fib.tal's output", stdout(), EXPECTED)
  end
end
