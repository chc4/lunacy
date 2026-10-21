-- `pairs`, `ipairs` and `next`, in loops long enough for JIT code. A table's traversal order is
-- unspecified, so what `pairs` finds is summed and counted.

local arr = {}
for i = 1, 50 do arr[i] = i * 2 end
local mixed = {10, 20, 30, x = 1, y = 2, z = 3}

local function ipairs_sum(t)
  local s = 0
  for i, v in ipairs(t) do s = s + i * v end
  return s
end

local function pairs_sum(t)
  local keys, values = 0, 0
  for k, v in pairs(t) do
    keys = keys + (type(k) == "number" and k or #k)
    values = values + v
  end
  return keys, values
end

local function key_count(t)
  local n = 0
  for _ in pairs(t) do n = n + 1 end
  return n
end

local a, b, c, d, e = 0, 0, 0, 0, 0
for _ = 1, 300 do
  a = a + ipairs_sum(arr)
  local k, v = pairs_sum(mixed)
  b, c = b + k, c + v
  d = d + key_count(arr)
end
print(a, b, c, d)

-- `ipairs` stops at the first nil, and reads raw: a metatable's `__index` isn't looked in.
local holes = setmetatable({1, 2, nil, 4}, {__index = {[3] = 3}})
local n = 0
for _ = 1, 300 do for i in ipairs(holes) do n = n + i end end
print(n)

-- Each field stored to while it's traversed, as Lua allows.
local fields = {p = 1, q = 2, r = 3}
for _ = 1, 300 do for k, v in pairs(fields) do fields[k] = v + 1 end end
print(fields.p + fields.q + fields.r)

-- `next` called directly: the first key, the key after one, and an empty table's.
local first = next(mixed)
print(first ~= nil, next({}), select("#", next({})))
local seen = 0
local key = next(mixed)
while key ~= nil do seen = seen + 1; key = next(mixed, key) end
print(seen)

-- Errors: not a table, and a key the table lacks.
local ok, err = pcall(pairs, nil)
print(ok, string.find(err, "table expected, got nil", 1, true) ~= nil)
ok, err = pcall(ipairs, 5)
print(ok, string.find(err, "table expected, got number", 1, true) ~= nil)
print(pcall(next, {}, "missing"))
-- EXPECT: 25755000	2700	19800	15000
-- EXPECT: 900
-- EXPECT: 906
-- EXPECT: true	nil	1
-- EXPECT: 6
-- EXPECT: false	true
-- EXPECT: false	true
-- EXPECT: false	invalid key to 'next'
