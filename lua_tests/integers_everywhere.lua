-- Numbers in either encoding anywhere (Note [Integer encoding]): integers
-- stored in tables and upvalues, returned and passed to natives, integer and
-- double keys that are the same key, a whole double compared with an integer
-- constant, integer ops overflowing into doubles, and a loop whose variable is
-- an integer on one way round and a double on another.
local bit = require("bit")

local captured = 0
local function keys(n)
  local t = {}
  for i = 1, n do
    t[i] = i * 2
    captured = captured + i
  end
  local half = 0.5
  -- The same keys, as doubles.
  local s = 0
  for i = 1, n do
    s = s + t[i * (half + half)]
  end
  t[0] = "zero"
  t[-1] = "minus one"
  return s, t[-0], t[0.5 * 0], t[-2 / 2], #t
end

local function compare(n)
  local hits = 0
  local x = 0.25
  for i = 1, n do
    x = x + 0.25
    if x == 1 then hits = hits + 1 end
    if x == 2 then hits = hits + 10 end
  end
  return hits, x
end

local function overflow(n)
  local x = 2147483600
  local y = -2147483600
  local z = 46341
  for i = 1, n do
    x = x + 10
    y = y - 10
  end
  return x, y, z * z, x % 7, bit.band(x, 255)
end

local function mixed(n)
  local v = 1
  local total = 0
  for i = 1, n do
    if i % 3 == 0 then v = v + 0.5 else v = v + 1 end
    total = total + v
  end
  return v, total
end

local function stored(n)
  local t = {}
  for i = 1, n do t[i] = i end
  t[3] = 3.5
  local sum = 0
  for i = 1, n do sum = sum + t[i] * 2 end
  return sum, tostring(t[2]), tostring(t[3])
end

local function run()
  captured = 0
  print(keys(6))
  print(captured)
  print(compare(8))
  print(overflow(10))
  print(mixed(10))
  print(stored(5))
end

run()
keys.__jit = 1
compare.__jit = 1
overflow.__jit = 1
mixed.__jit = 1
stored.__jit = 1
run()
-- EXPECT: 42	zero	zero	minus one	6
-- EXPECT: 21
-- EXPECT: 11	2.25
-- EXPECT: 2147483700	-2147483700	2147488281	5	52
-- EXPECT: 9.5	57.5
-- EXPECT: 31	2	3.5
-- EXPECT: 42	zero	zero	minus one	6
-- EXPECT: 21
-- EXPECT: 11	2.25
-- EXPECT: 2147483700	-2147483700	2147488281	5	52
-- EXPECT: 9.5	57.5
-- EXPECT: 31	2	3.5
