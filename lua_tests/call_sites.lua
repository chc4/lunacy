-- A call to a Lua function the context knows enters a version of it for its
-- arguments' types (Note [Call sites]). Each part runs a call site with
-- arguments whose types change, missing and extra arguments, recursion, tables
-- with shapes, and more functions at one site than it specializes.
-- (No `return f(x)`: that is a tail call.)

local function add(a, b)
  local r = a + b
  return r
end

-- One site, argument types changing: integers, doubles, then both.
local function sums(n)
  local total = 0
  for i = 1, n do
    local x = i
    if i > n / 2 then x = i + 0.5 end
    total = total + add(x, i)
  end
  return total
end
print(sums(20), sums(21))

-- Missing arguments are nil; extra ones are dropped.
local function describe(a, b, c)
  local n = 0
  if a ~= nil then n = n + 1 end
  if b ~= nil then n = n + 10 end
  if c ~= nil then n = n + 100 end
  return n
end
local function arities(n)
  local total = 0
  for i = 1, n do
    total = total + describe() + describe(i) + describe(i, i) + describe(i, i, i) + describe(i, i, i, i)
  end
  return total
end
print(arities(10))

-- Arguments up to the top a native window op left.
local band = bit.band
local function low(x, y)
  local r = x
  if y ~= nil then r = r + y end
  return r
end
local function tops(n)
  local total = 0
  for i = 1, n do
    total = total + low(band(i, 7))
  end
  return total
end
print(tops(40))

-- Recursion and mutual recursion.
local function fib(n)
  if n < 2 then return n end
  local a = fib(n - 1)
  local b = fib(n - 2)
  return a + b
end
local is_odd
local function is_even(n)
  if n == 0 then return true end
  local r = is_odd(n - 1)
  return r
end
is_odd = function(n)
  if n == 0 then return false end
  local r = is_even(n - 1)
  return r
end
print(fib(20), is_even(10), is_odd(7), is_even(7))

-- A table whose fields the caller knows, passed and written by the callee.
local function bump(t, by)
  t.x = t.x + by
  t.y = t.y * 2
end
local function shapes(n)
  local t = { x = 1, y = 1 }
  local seen = 0
  for i = 1, n do
    seen = seen + t.x
    bump(t, i)
    seen = seen + t.x
  end
  return seen, t.x, t.y
end
print(shapes(10))

-- More functions at one site than it specializes, each a different prototype.
local fs = {
  function(x) local r = x + 1 return r end,
  function(x) local r = x * 2 return r end,
  function(x) local r = x - 3 return r end,
  function(x) local r = x * x return r end,
  function(x) local r = -x return r end,
  function(x) local r = x + 10 return r end,
  function(x) local r = x * 3 return r end,
  function(x) local r = x - 1 return r end,
}
local function dispatch(n)
  local total = 0
  for i = 1, n do
    local f = fs[(i % #fs) + 1]
    total = total + f(i)
  end
  return total
end
print(dispatch(80), dispatch(81))

-- Closures of one prototype, each with its own upvalue, called at one site.
local function counter(start)
  local count = start
  return function(by)
    count = count + by
    return count
  end
end
local function counters(n)
  local cs = { counter(0), counter(100), counter(1000) }
  local total = 0
  for i = 1, n do
    local c = cs[(i % 3) + 1]
    total = total + c(i)
  end
  return total, cs[1](0), cs[2](0), cs[3](0)
end
print(counters(30))
-- EXPECT: 425	467.5
-- EXPECT: 2340
-- EXPECT: 140
-- EXPECT: 6765	true	true	false
-- EXPECT: 405	56	1024
-- EXPECT: 23820	23982
-- EXPECT: 12815	165	245	1155
