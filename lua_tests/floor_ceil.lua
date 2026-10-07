-- math.floor and math.ceil of one number keeping one result are compiled by
-- their generator (see Note [Native generators]): of an integer, the integer;
-- of a double, an integer while it fits, as an integer op's result is, until
-- one doesn't, which rebuilds the call to compute in doubles (Note
-- [Optimistic ops]). Results past i32, -0, and any other call stay doubles.
local floor, ceil = math.floor, math.ceil

local function sums(n, scale)
  local s = 0
  for i = 1, n do
    local x = (i - n / 2) * scale + 0.25
    s = s + floor(x) + ceil(x) + floor(i) + ceil(-i)
  end
  return s
end

local function edges()
  floor(1.5)
  return floor(2^40 + 0.5), ceil(-2^31 - 0.5), ceil(-0.5), floor(-0.5), floor(7, 8)
end

print(sums(100, 1.5), sums(100, 2^28), edges())
sums.__jit = 1
edges.__jit = 1
print(sums(100, 1.5), sums(100, 2^28), sums(100, 1.5), edges())
-- EXPECT: 200	26843545700	1099511627776	-2147483648	-0	-1	7
-- EXPECT: 200	26843545700	200	1099511627776	-2147483648	-0	-1	7
