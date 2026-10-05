-- How much machine code LuaJIT's JIT generates for a benchmark, and whether it
-- flushes its traces while running: runs the benchmark's bytecode (`just
-- _luajitc`), `run_iter(times)`, watching each trace event (as `-jv` does):
-- each trace made, aborted, and every flush of all traces, which LuaJIT does
-- when its machine code area is full, among other reasons. Reports, per span
-- between flushes, the traces made, their machine code's bytes and the span of
-- addresses it covers; then the run's totals, and the traces alive at its end.
--
--     luajit tools/luajit_mcode.lua working/<benchmark>.luajit.bin <times>
local jutil = require("jit.util")
local args = {...}

local spans, span = {}, nil
local function new_span()
  span = { traces = 0, aborts = 0, bytes = 0, largest = 0, low = math.huge, high = 0 }
  spans[#spans + 1] = span
end
new_span()

jit.attach(function(what, tr)
  if what == "flush" then
    new_span()
  elseif what == "abort" then
    span.aborts = span.aborts + 1
  elseif what == "stop" then
    local mcode, addr = jutil.tracemc(tr)
    if mcode then
      local size = #mcode
      span.traces = span.traces + 1
      span.bytes = span.bytes + size
      if size > span.largest then span.largest = size end
      if addr < span.low then span.low = addr end
      if addr + size > span.high then span.high = addr + size end
    end
  end
end, "trace")

dofile(args[1])
run_iter(tonumber(args[2]))
-- The report's own loops make no traces.
jit.off()

local traces, bytes, aborts = 0, 0, 0
for i, s in ipairs(spans) do
  traces, bytes, aborts = traces + s.traces, bytes + s.bytes, aborts + s.aborts
  local covers = s.traces > 0 and string.format(", over %d bytes of addresses", s.high - s.low) or ""
  print(string.format("%s %d: %d traces, %d aborted, %d bytes of machine code, largest %d bytes%s",
    i == 1 and "start" or "after flush", i - 1, s.traces, s.aborts, s.bytes, s.largest, covers))
end
print(string.format("%d flushes; %d traces made, %d aborted, %d bytes of machine code in all", #spans - 1, traces, aborts, bytes))

-- The traces alive at the end. Trace numbers run from 1; a flushed or
-- never-made trace has no machine code.
local alive, alive_bytes = 0, 0
for tr = 1, 65535 do
  if not jutil.traceinfo(tr) then break end
  local mcode = jutil.tracemc(tr)
  if mcode then
    alive, alive_bytes = alive + 1, alive_bytes + #mcode
  end
end
print(string.format("alive at the end: %d traces, %d bytes of machine code", alive, alive_bytes))
