-- Straight-line arithmetic on numbers: once its arguments' guards have passed,
-- the function's body is one block of window ops.
local function f(a, b, c, d)
  local x = a * b + c
  local y = x * d - a
  local z = (x + y) * (b - d)
  return x + y + z
end
print(f(2, 3, 4, 5))
f.__jit = 1
print(f(2, 3, 4, 5))
print(f(1, 2, 3, 4))
-- EXPECT: -58
-- EXPECT: -58
-- EXPECT: -24
