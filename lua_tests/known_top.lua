-- A native's window op taking every result (C = 0), the last argument of a call
-- taking its arguments up to the top (B = 0): another window op (euler14's
-- step), a native without one, a return, a table constructor, and a Lua
-- function given exactly its arguments. See Note [Known top].
local bit = require("bit")
local bnot, bor, band = bit.bnot, bit.bor, bit.band
local shl, shr = bit.lshift, bit.rshift

local function pair(x, y, z) return z == nil and y end

local function run(n)
  local j = n
  for _ = 1, 6 do
    j = bor(band(shr(j, 1), band(j, 1) - 1), band(shl(j, 1) + j + 1, bnot(band(j, 1) - 1)))
    print(j)
  end
  print(band(j, 7), bnot(j))
  local t = {1, band(j, 3)}
  print(#t, t[2])
  print(pair(1, bor(j, 1)))
  return 1, band(j, 15)
end

print(run(27))
run.__jit = 1
print(run(27))
-- EXPECT: 82
-- EXPECT: 41
-- EXPECT: 124
-- EXPECT: 62
-- EXPECT: 31
-- EXPECT: 94
-- EXPECT: 6	-95
-- EXPECT: 2	2
-- EXPECT: 95
-- EXPECT: 1	14
-- EXPECT: 82
-- EXPECT: 41
-- EXPECT: 124
-- EXPECT: 62
-- EXPECT: 31
-- EXPECT: 94
-- EXPECT: 6	-95
-- EXPECT: 2	2
-- EXPECT: 95
-- EXPECT: 1	14
