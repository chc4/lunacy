-- A store into a metamethod's field that keeps its type changes what lookups through it find: an
-- `__index` table swapped for one whose chain is shorter or longer, and an `__add` swapped in a
-- table a chain passes. Each loop runs long enough for JIT code.

local function sum(n, f)
  local s = 0
  for i = 1, n do s = s + f(i) end
  return s
end

-- `o.k` from two hops down, then one, then two again.
local far = setmetatable({}, {__index = {k = 2}})
local near = {k = 3}
local cmt = {__index = far}
local o = setmetatable({}, cmt)
print(sum(900, function(i)
  if i == 300 then cmt.__index = near end
  if i == 600 then cmt.__index = far end
  return o.k
end))

-- A table down the chain gains the key the lookup found past it.
local deep = {k = 1}
local mid = setmetatable({}, {__index = deep})
local top = setmetatable({}, {__index = mid})
print(sum(600, function(i)
  if i == 300 then mid.k = 5 end
  return top.k
end))

-- An `__add` swapped for another function, through its hash key, then through a key the store
-- doesn't know.
local amt = {__add = function(a, b) return 1 end}
local a = setmetatable({}, amt)
local event = "__" .. "add"
print(sum(900, function(i)
  if i == 300 then amt.__add = function(x, y) return 2 end end
  if i == 600 then amt[event] = function(x, y) return 3 end end
  return a + i
end))
-- EXPECT: 2100
-- EXPECT: 1804
-- EXPECT: 1802
