-- Number keys outside the array part (zero, negatives, fractions) are hash
-- keys, apart from the integer keys next to them; nsieve_bit indexes from 0.
local t = {}
t[0] = "zero"; t[-1] = "minus one"; t[1.5] = "one and a half"
t[1] = "one"; t[2] = "two"
print(t[0], t[-1], t[1.5], t[1], t[2], #t)
t[0] = nil
print(t[0], t[1])

local bit = require("bit")
local band, rshift, rol = bit.band, bit.rshift, bit.rol
local function nsieve(p, m)
  local count = 0
  for i=0,rshift(m, 5) do p[i] = -1 end
  for i=2,m do
    if band(rshift(p[rshift(i, 5)], i), 1) ~= 0 then
      count = count + 1
      for j=i+i,m,i do
        local jx = rshift(j, 5)
        p[jx] = band(p[jx], rol(-2, j))
      end
    end
  end
  return count
end
print(nsieve({}, 100), nsieve({}, 10000))
nsieve.__jit = 1
print(nsieve({}, 100), nsieve({}, 10000))
-- EXPECT: zero	minus one	one and a half	one	two	2
-- EXPECT: nil	one
-- EXPECT: 25	1229
-- EXPECT: 25	1229
