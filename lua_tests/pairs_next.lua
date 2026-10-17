-- `ipairs`, `pairs`, `next` and `select`. A hash part's order is the
-- implementation's own, so what is printed of it doesn't depend on it.

-- ipairs: the array part up to its first nil.
local function isum(t)
  local n, s = 0, 0
  for i, v in ipairs(t) do
    n = n + 1
    s = s + i * v
  end
  return n, s
end
print(isum({1, 2, 3, 4}))
print(isum({5, 6, nil, 8}))
print(isum({}))
-- EXPECT: 4	30
-- EXPECT: 2	17
-- EXPECT: 0	0

-- pairs: every entry, of both parts, nil entries left out.
local function count(t)
  local n, keys, s = 0, {}, 0
  for k, v in pairs(t) do
    n = n + 1
    keys[#keys + 1] = tostring(k)
    if type(v) == "number" then s = s + v end
  end
  table.sort(keys)
  return n, table.concat(keys, ","), s
end
local t = {10, 20, 30, x = 1, y = 2, [2.5] = 3}
print(count(t))
t.x = nil
t[2] = nil
print(count(t))
print(count({}))
-- EXPECT: 6	1,2,2.5,3,x,y	66
-- EXPECT: 4	1,2.5,3,y	45
-- EXPECT: 0		0

-- next: nil for an empty table, and from a key it gave.
print(next({}))
local k, v = next({a = 7})
print(k, v, next({a = 7}, "a"))
-- EXPECT: nil
-- EXPECT: a	7	nil

-- An entry set while walking, to a key it already has, keeps the walk whole.
local u = {a = 1, b = 2, c = 3}
local seen = 0
for k in pairs(u) do
  u[k] = 0
  seen = seen + 1
end
print(seen, u.a + u.b + u.c)
-- EXPECT: 3	0

-- select: from the nth argument, from the end for a negative n, or the count.
print(select(2, "a", "b", "c"))
print(select(-1, "a", "b", "c"))
print(select("#", "a", nil, "c"))
print(select("#"))
print(select("#", select(4, "a", "b", "c")))
-- EXPECT: b	c
-- EXPECT: c
-- EXPECT: 3
-- EXPECT: 0
-- EXPECT: 0

-- In a compiled loop.
local function walk(t)
  local s = 0
  for _, v in pairs(t) do s = s + v end
  for _, v in ipairs(t) do s = s + v end
  return s
end
walk.__jit = 1
local w = {1, 2, 3, p = 10, q = 20}
for _ = 1, 3 do print(walk(w)) end
-- EXPECT: 42
-- EXPECT: 42
-- EXPECT: 42
