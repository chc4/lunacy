-- string.byte's call is compiled by its generator (see Note [Native generators]):
-- byte(s, i, j) keeping one to four results reads them where its range is in
-- the string, and any other call is the native's: a range past the string's
-- end (its results nil), positions below one or counted from the end, a
-- number for the string, every result kept, and another count of arguments.
local byte = string.byte

local function reads(s, n)
  local sum = 0
  for i = 1, n do
    local a = byte(s, i, i)
    local b, c = byte(s, i, i + 1)
    local d, e, f = byte(s, i, i + 2)
    local g, h, k, l = byte(s, i, i + 3)
    sum = sum + a + b + (c or 1000) + d + (e or 1000) + (f or 1000)
    sum = sum + g + (h or 1000) + (k or 1000) + (l or 1000)
  end
  return sum
end

local function others(s)
  local sum = 0
  for i = 1, 20 do
    local p, q = byte(s, 0, 1)
    local r = byte(s, -2, -1)
    local t, u = byte(12345, 2, 3)
    sum = sum + (p or 1000) + (q or 1000) + r + t + u
    sum = sum + #{byte(s, 1, -1)} + byte(s) + byte(s, 3)
  end
  return sum
end

local s = "the quick brown fox"
print(reads(s, #s), others(s))
reads.__jit = 1
others.__jit = 1
print(reads(s, #s), others(s))
-- EXPECT: 27321	31280
-- EXPECT: 27321	31280
