-- An integer add whose result fits on some runs and overflows on others: once
-- it overflows it computes in doubles, and every result before and after is
-- still the sum, whether or not it would have fit. In a function, and inline
-- in a loop.
local bit = require("bit")

local function add(a, b)
  return a + b
end

local function sums(from, to)
  local out = {}
  for i = from, to do
    out[#out + 1] = add(bit.lshift(i, 27), bit.lshift(1, 30))
  end
  return table.concat(out, " ")
end

local function inline(from, to)
  local out = {}
  local y = bit.lshift(1, 30)
  for i = from, to do
    local x = bit.lshift(i, 27)
    out[#out + 1] = x + y
  end
  return table.concat(out, " ")
end

print(sums(1, 12))
print(sums(1, 3))
print(inline(1, 12))
print(inline(1, 3))
-- EXPECT: 1207959552 1342177280 1476395008 1610612736 1744830464 1879048192 2013265920 2147483648 2281701376 2415919104 2550136832 2684354560
-- EXPECT: 1207959552 1342177280 1476395008
-- EXPECT: 1207959552 1342177280 1476395008 1610612736 1744830464 1879048192 2013265920 2147483648 2281701376 2415919104 2550136832 2684354560
-- EXPECT: 1207959552 1342177280 1476395008
