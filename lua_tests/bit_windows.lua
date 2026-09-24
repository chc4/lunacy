-- The bit library's natives run as window ops where a call is known to be to
-- them (see Note [Native windows]): one result, from one or two arguments.
-- Other arities stay native calls. Each checksums every operation over
-- operands including negatives, fractions and shifts past 31.
local bit = require("bit")
local tobit, bnot, bswap = bit.tobit, bit.bnot, bit.bswap
local band, bor, bxor = bit.band, bit.bor, bit.bxor
local lshift, rshift, arshift, rol, ror = bit.lshift, bit.rshift, bit.arshift, bit.rol, bit.ror

local function first(v) return v end
local function ops(n)
  local sum = 0
  for i = 1, n do
    local x, y = i * 2654435761 - 12345, (i * 7) % 40 - 3
    sum = sum + tobit(x) % 1000 + bnot(x) % 1000 + bswap(i) % 1000
    sum = sum + band(x, y) % 1000 + bor(x, y) % 1000 + bxor(x, y) % 1000
    sum = sum + lshift(x, y) % 1000 + rshift(x, y) % 1000 + arshift(x, y) % 1000
    sum = sum + rol(x, y) % 1000 + ror(x, y) % 1000
    -- Other shapes of call are native calls: three arguments, no results
    -- kept, two results kept, every result passed on.
    sum = sum + band(x, y, 255) + bor(x, y, 1) % 1000
    bxor(x, y)
    local p, q = band(x, 255)
    sum = sum + p + (q == nil and 1 or 0)
    sum = sum + first(rol(x, 1)) % 1000
  end
  return sum
end
print(ops(200), tobit(2^32 + 5.5), bnot(0), bswap(1))
ops.__jit = 1
print(ops(200), tobit(2^32 + 5.5), bnot(0), bswap(1))
-- EXPECT: 1233354	6	-1	16777216
-- EXPECT: 1233354	6	-1	16777216
