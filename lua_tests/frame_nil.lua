-- A call's frame is nil past its arguments, up to the callee's max stack: luac
-- emits no LOADNIL for a local declared at a function's first instruction, so a
-- callee reads that nil. Each caller leaves values in slots the callee's frame
-- then overlaps, in the interpreter and, called often, in JIT code.

local function fresh() local x; return x end
local function fresh2(a) local x, y; return a, x, y end

local function after_temps()
  do local a, b, c, d = 1, 2, 3, 4 end
  local r = fresh()
  return r
end

local function after_temps2()
  do local a, b, c, d, e = "a", "b", "c", "d", "e" end
  local p, q, r = fresh2(7)
  return p, q, r
end

print(after_temps())
print(after_temps2())

local stale = 0
for i = 1, 200 do
  if after_temps() ~= nil then stale = stale + 1 end
  local p, q, r = after_temps2()
  if p ~= 7 or q ~= nil or r ~= nil then stale = stale + 1 end
end
print(stale)
-- EXPECT: nil
-- EXPECT: 7	nil	nil
-- EXPECT: 0
