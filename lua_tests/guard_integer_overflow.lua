-- Integer arithmetic is guarded by a dynamic test that the result fits the
-- integer encoding (Note [Dynamic guards]); a result that doesn't is computed
-- as a double. Each loop runs the fitting side first, until it's compiled,
-- then crosses the 32-bit boundary so the guard fails, and keeps going.

-- ADD of two registers, crossing 2^31 upwards.
local function add_rr(start, step, n)
  local x = start
  for i = 1, n do
    x = x + step
  end
  return x
end
print(add_rr(2147483000, 7, 200), add_rr(0, 1, 200))

-- SUB crossing -2^31 downwards, and back.
local function sub_rr(start, step, n)
  local x = start
  local lowest = start
  for i = 1, n do
    x = x - step
    if x < lowest then lowest = x end
  end
  for i = 1, n do
    x = x + step
  end
  return lowest, x
end
print(sub_rr(-2147483000, 9, 200))

-- MUL of registers, overflowing partway through a doubling.
local function mul_rr(n)
  local x, two = 3, 2
  local seen = 0
  for i = 1, n do
    x = x * two
    seen = seen + 1
  end
  return x, seen
end
print(mul_rr(40))

-- Constant operands: x + K, K + x, x * K.
local function add_k(n)
  local a, b, c = 2147483600, 2147483600, 1
  for i = 1, n do
    a = a + 1
    b = 1 + b
    -- 3^28 crosses 2^31, and stays short of 1e14, past which Lua prints an
    -- exponent.
    if i <= 28 then c = c * 3 end
  end
  return a, b, c
end
print(add_k(60))

-- The overflowed value used as an integer again: compared, indexed with,
-- added to integers.
local function reuse(n)
  local x = 2147483640
  local count = 0
  local t = {}
  for i = 1, n do
    x = x + 1
    if x > 2147483647 then count = count + 1 end
    t[i] = x - 2147483600
  end
  local sum = 0
  for i = 1, n do sum = sum + t[i] end
  return x, count, sum
end
print(reuse(30))

-- MOD by zero fails the guard; its result is NaN.
local function mod(n)
  local nans, sum = 0, 0
  for i = 1, n do
    local d = i % 5
    local r = 17 % d
    if r ~= r then nans = nans + 1 else sum = sum + r end
  end
  return nans, sum
end
print(mod(100))

-- Negative operands and MOD's sign.
local function mod_signs(n)
  local sum = 0
  for i = -n, n do
    local d = i
    if d == 0 then d = 1 end
    sum = sum + (i % 7) + (7 % d)
  end
  return sum
end
print(mod_signs(50))

-- A value alternating between fitting and not, so the guard's two sides both
-- run hot.
local function alternate(n)
  local big, small = 2147483647, 5
  local total = 0
  for i = 1, n do
    local base = small
    if i % 2 == 0 then base = big end
    total = total + (base + 1) - base
  end
  return total
end
print(alternate(100))
-- EXPECT: 2147484400	200
-- EXPECT: -2147484800	-2147483000
-- EXPECT: 3298534883328	40
-- EXPECT: 2147483660	2147483660	22876792454961
-- EXPECT: 2147483670	23	1665
-- EXPECT: 20	80
-- EXPECT: -348
-- EXPECT: 100
