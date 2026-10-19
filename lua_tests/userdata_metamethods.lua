-- Arithmetic on userdata calls its metatable's handler, as on tables, alongside fields read raw
-- from its `__index` table. Each loop runs long enough for JIT code.

local function sum(n, f)
  local s = 0
  for i = 1, n do s = s + f(i) end
  return s
end

local u = newproxy(true)
local mt = getmetatable(u)
mt.__index = {v = 3, __add = 100}
local function num(x) return type(x) == "userdata" and 10 or x end
mt.__add = function(a, b) return num(a) + num(b) end
mt.__mul = function(a, b) return num(a) * num(b) end
mt.__unm = function(a) return -num(a) end

-- Each side, two userdata, unary minus, and a field from `__index`, whose `__add` isn't the
-- handler.
print(sum(300, function(i) return (u + i) + (i + u) + (u + u) + (u * 2) + (-u) + u.v + u.__add end))

-- A handler swapped partway through.
print(sum(600, function(i)
  if i == 300 then mt.__add = function(a, b) return 1 end end
  return u + i
end))

-- A handler but no `__index`.
local bare = newproxy(true)
getmetatable(bare).__sub = function(a, b) return 7 end
print(sum(300, function(i) return bare - i end))

-- No handler: an error.
local ok, err = pcall(function() return newproxy(true) + 1 end)
print(ok, string.find(err, "attempt to perform arithmetic on a userdata value", 1, true) ~= nil)

-- A userdata's length is its handler's, called with it and nil; a table's is its own, whatever
-- its metatable has.
mt.__len = function(a, b) return (a == u and b == nil) and 4 or -1 end
local t = setmetatable({1, 2}, {__len = function() return 9 end})
print(sum(300, function(i) return #u + #t end))
ok, err = pcall(function() return #newproxy(true) end)
print(ok, string.find(err, "attempt to get length of a userdata value", 1, true) ~= nil)
-- EXPECT: 136200
-- EXPECT: 48141
-- EXPECT: 2100
-- EXPECT: false	true
-- EXPECT: 1800
-- EXPECT: false	true
