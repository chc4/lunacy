-- Uxntal's Takeuchi function example (varvara/roms/tak.tal) on the Lua Varvara
-- emulator: tak(24, 20, 11) in bytes, which prints its stacks, the result on
-- top of the working stack. Deep recursion through the return stack.

local bench = require("uxn_bench")
local ROM = require("roms.tak")

function run_iter(n)
  for _ = 1, n do
    local emu, _, stderr = bench.machine(ROM)
    emu.boot(false)
    bench.check("tak.tal's stacks", stderr(), "WST 00 00 00 00 00 00 00|0c < \nRST 00 00 00 00 00 00 00 00|< \n")
  end
end
