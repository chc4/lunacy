-- The integer encoding of numbers (see Note [Integers]): integers across
-- arithmetic, compares and loops, leaving through calls, returns, tables,
-- globals and jumps as they are, and doubles where they stop being integers
-- (overflow, -0, fractions, NaN).
local function id(x) return x end

local function arith(n)
  local big, small, m = 2147483647, -2147483648, 65536
  local s = 0
  for i = 1, n do
    -- Out of the i32 range and back.
    s = s + (big + i) - (small - i) + m * m / 65536 - (big + i - i)
    -- Zero times a negative number is -0: 1 / -0 is -inf.
    local z = 0 * -i
    s = s + (1 / z < 0 and 1 or 0)
    -- Floored MOD, and MOD by zero.
    s = s + (7 + i) % -3 + (-7 - i) % 3 + (i * 5) % 4
    local nan = i % 0
    s = s + (nan ~= nan and 1 or 0)
    -- Integers with doubles.
    s = s + i * 0.5 + (i < 2.5 and 1 or 0) + (i + 0.25 > 2 and 1 or 0) + (i == 2.0 and 1 or 0)
  end
  return s
end
print(arith(6))
arith.__jit = 1
print(arith(6))

-- Integers leaving through calls, returns, tables and globals, and temporaries
-- carried across jumps.
local function carry(n)
  local t, h = {}, {}
  local acc = 0
  for i = 1, n do
    t[i] = i
    h.last = i
    glob = i
    local v = i > 2 and 5 or 7
    acc = acc + id(v) + t[i] + h.last + glob
    -- Overflows after a few iterations, then stays a double.
    acc = acc + 1000000000
  end
  return acc, #t, h.last + 1, glob * 2, t[n] / 2
end
print(carry(8))
carry.__jit = 1
print(carry(8))

-- Loops counting down, by fractions, and past the i32 range.
local function steps()
  local s = 0
  for i = 10, 1, -3 do s = s + i end
  for i = 1, 2, 0.25 do s = s + i end
  for i = 2147483640, 2147483647 do s = s + 1 end
  for i = -2147483647, -2147483648, -1 do s = s + 1 end
  for i = 3, 1 do s = s + 100 end
  return s
end
print(steps())
steps.__jit = 1
print(steps())
-- EXPECT: 12885295185.5
-- EXPECT: 12885295185.5
-- EXPECT: 8000000152	8	9	16	4
-- EXPECT: 8000000152	8	9	16	4
-- EXPECT: 39.5
-- EXPECT: 39.5
