-- Vararg functions: extra arguments read into a table, into fixed locals
-- (padded with nil), and returned; more and fewer arguments than the fixed
-- parameters; a vararg function calling another with every result of a call; one
-- whose fixed parameter a closure captures; one recursing. Once, and in a loop run
-- often enough for JIT code.

local function count(...)
  local t = {...}
  return #t
end

local function first(a, ...)
  local x, y = ...
  return a, x, y
end

local function pass(...)
  return ...
end

local function sum(...)
  local s = 0
  local t = {...}
  for i = 1, #t do s = s + t[i] end
  return s
end

local function capture(n, ...)
  local get = function() return n end
  local total = sum(...)
  return get() + total
end

local function down(n, ...)
  if n == 0 then
    local r = count(...)
    return r
  end
  local r = down(n - 1, n, ...)
  return r
end

local function run(k)
  local a, x, y = first(k)
  local b, x2, y2 = first(k, 2, 3, 4)
  local p1, p2, p3 = pass(k, nil, 3)
  local joined = table.concat({
    count(), count(k), count(k, k, k), tostring(a) .. tostring(x) .. tostring(y),
    b .. x2 .. y2, tostring(p1) .. tostring(p2) .. tostring(p3),
    sum(pass(1, 2, 3, k)), count(pass()), capture(k, 1, 2), capture(k), down(5), down(3, k, k),
  }, " ")
  return joined
end

local first_run = run(7)
local same = true
for i = 1, 300 do
  if run(7) ~= first_run then same = false end
end
print(first_run)
print(run(1))
print(same)
-- EXPECT: 0 1 3 7nilnil 723 7nil3 13 0 10 7 5 5
-- EXPECT: 0 1 3 1nilnil 123 1nil3 7 0 4 1 5 5
-- EXPECT: true
