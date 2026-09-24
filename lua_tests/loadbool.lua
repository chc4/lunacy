-- LOADBOOL: a boolean constant, and a comparison's result as a value, which
-- compiles to a pair of LOADBOOLs, the first skipping the second.
local function f(a, b)
  local t = true
  local lt = a < b
  local le = a <= b
  local n = 0
  if t then n = n + 1 end
  if lt then n = n + 10 end
  if le then n = n + 100 end
  return n
end
print(f(1, 2))
print(f(2, 2))
f.__jit = 1
print(f(1, 2))
print(f(2, 2))
print(f(3, 2))
-- EXPECT: 111
-- EXPECT: 101
-- EXPECT: 111
-- EXPECT: 101
-- EXPECT: 1
