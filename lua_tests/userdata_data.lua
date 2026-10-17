-- Userdata with native data (the test runner's `make_counter`): each counter's
-- count is its own, kept by the native that bumps it, across calls, with two
-- counters bumped in turn, and in a loop run often enough for JIT code; and a
-- counter dropped and collected while another is bumped.
local a, b = make_counter(), make_counter()
print(a:bump(), a:bump(), b:bump())
local function bump(x, y, n)
  local sum = 0
  for i = 1, n do sum = sum + x:bump() + y:bump() end
  return sum
end
print(bump(a, b, 1000))
for i = 1, 100 do make_counter():bump() end
collectgarbage("collect")
print(a:bump(), b:bump())
-- EXPECT: 1	2	1
-- EXPECT: 1004000
-- EXPECT: 1003	1002
