-- Arithmetic on tables calls their metatable's handler: the left operand's, else the right's,
-- with both operands. Each loop runs long enough for JIT code, and a handler replaced while one
-- runs is called from then on.

local mt = {}
mt.__add = function(a, b) return (type(a) == "table" and a.v or a) + (type(b) == "table" and b.v or b) end
mt.__sub = function(a, b) return a.v - b end
mt.__mul = function(a, b) return a.v * b.v end
mt.__div = function(a, b) return a.v / b end
mt.__mod = function(a, b) return a.v % b end
mt.__pow = function(a, b) return a.v ^ b end
mt.__unm = function(a) return -a.v end
local function new(v) return setmetatable({v = v}, mt) end

local function sums(n)
  local t, u, s = new(2), new(3), 0
  for i = 1, n do
    s = s + (t + i) + (i + t) + (t + u) + (t - 1) + (t * u) + (t / 2) + (t % 2) + (t ^ 2) + (-t)
  end
  return s
end
print(sums(200))

-- Only the right operand has a handler.
local plain = {v = 5}
local function right(n)
  local s = 0
  for i = 1, n do s = s + (plain + new(i)) end
  return s
end
print(pcall(right, 1))
print((function(n) local s = 0 for i = 1, n do s = s + (1 + new(i)) end return s end)(200))

-- The left operand's metatable lacks the handler: the right one's is used.
local other = setmetatable({v = 4}, {})
print((function(n) local s = 0 for i = 1, n do s = s + (other + new(i)) end return s end)(200))

-- A handler replaced partway through a loop.
local function replaced(n)
  local t, s = new(1), 0
  for i = 1, n do
    if i == n / 2 then mt.__add = function(a, b) return 1000 end end
    s = s + (t + i)
  end
  return s
end
print(replaced(800))

-- A handler replaced by another function, the field's type kept, through the metatable's hash key
-- and through a key the store doesn't know.
local smt = {__add = function(a, b) return 1 end}
local so = setmetatable({}, smt)
local function swapped(n, key)
  local s = 0
  for i = 1, n do
    s = s + (so + i)
    if i == n / 4 then smt.__add = function(a, b) return 2 end end
    if i == n / 2 then smt[key] = function(a, b) return 3 end end
  end
  return s
end
print(swapped(800, "__add"))

-- A field found through `__index` before an `__add` of the same table.
local class = {k = 7}
local cmt = {__index = class, __add = function(a, b) return a.k + b end}
local function chained(n)
  local o, s = setmetatable({}, cmt), 0
  for i = 1, n do s = s + o.k + (o + i) end
  return s
end
print(chained(200))

-- No handler: an error.
local ok, err = pcall(function() return {} + 1 end)
print(ok, string.find(err, "attempt to perform arithmetic on a table value", 1, true) ~= nil)
ok, err = pcall(function() local x return x * 2 end)
print(ok, string.find(err, "attempt to perform arithmetic on", 1, true) ~= nil)
-- EXPECT: 44000
-- EXPECT: true	6
-- EXPECT: 20300
-- EXPECT: 20900
-- EXPECT: 481199
-- EXPECT: 1800
-- EXPECT: 22900
-- EXPECT: false	true
-- EXPECT: false	true
