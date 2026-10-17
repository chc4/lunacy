-- A function inlined into a loop writing two fields of a table its caller
-- passed it, of which the caller knows one: the caller reads the field before
-- and after each call. Once, and in a loop run often enough for JIT code.

local function bump(t, by)
  t.x = t.x + by
  t.y = t.y * 2
end
local function shapes(n)
  local t = { x = 1, y = 1 }
  local seen = 0
  for i = 1, n do
    seen = seen + t.x
    bump(t, i)
    seen = seen + t.x
  end
  return seen, t.x, t.y
end
print(shapes(3))
print(shapes(10))
-- EXPECT: 20	7	8
-- EXPECT: 405	56	1024
