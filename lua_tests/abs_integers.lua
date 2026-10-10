-- `math.abs` of integers, which keeps them integers, and of doubles: positive and
-- negative ones and zero, then the most negative integer, whose absolute value isn't
-- one, at the same call, summed with the rest and compared. Once, and in a loop run
-- often enough for JIT code, which meets the most negative integer only last.

local abs = math.abs

local function run(n, low)
  local sum, halves, last = 0, 0, 0
  for i = 1, n do
    local x = (i % 7) - 3
    if i == n then
      x = low
    end
    last = abs(x)
    sum = sum + last
    halves = halves + abs(x * 0.5)
  end
  return sum, halves, last, last > 2147483647, abs(-0.0) == 0
end

print(run(10, -2147483647 - 1))
print(run(1000, -2147483647 - 1))
-- EXPECT: 2147483663	1073741831.5	2147483648	true	true
-- EXPECT: 2147485358	1073742679	2147483648	true	true
