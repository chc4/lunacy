-- How much machine code LuaJIT's JIT generates for a benchmark: runs the
-- benchmark's bytecode (`just _luajitc`), `run_iter(times)`, then sums the size
-- of each trace's machine code from `jit.util`.
--
--     luajit tools/luajit_mcode.lua working/<benchmark>.luajit.bin <times>
local jutil = require("jit.util")
local args = {...}

dofile(args[1])
run_iter(tonumber(args[2]))

local traces, bytes, largest = 0, 0, 0
-- Trace numbers run from 1; a flushed or never-made trace has no machine code.
for tr = 1, 65535 do
  local info = jutil.traceinfo(tr)
  if not info then break end
  -- The trace's machine code, as a string.
  local mcode = jutil.tracemc(tr)
  if mcode then
    local size = #mcode
    traces = traces + 1
    bytes = bytes + size
    if size > largest then largest = size end
  end
end
print(string.format("%d traces, %d bytes of machine code, largest %d bytes", traces, bytes, largest))
