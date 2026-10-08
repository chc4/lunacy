-- Calls of small Lua functions are compiled into their callers' code (see Note
-- [Inlined calls]): with upvalues, keeping fewer and more results than they
-- return, keeping every result, with arguments up to the top, returning every
-- result of a call, calling a function that isn't inlined, inlining another in
-- turn, making a closure, reading a table's fields, and raising an error a
-- protected call around their caller catches, which closes the upvalues the
-- caller opened.
local bit = require("bit")
local band, bxor = bit.band, bit.bxor

local function mix(a, b) return bxor(a, band(b, 255)) + 1 end
local function pair(a) return a, a + 1 end
local function triple(a) return a, a * 2, a * 3 end
local function inner(x) return x * 3 end
local function outer(x) return inner(x) + inner(x + 1) end
local function looping(n) local s = 0 for i = 1, n do s = s + i end return s end
local function calls_loop(n) return looping(n) + 1 end
local function counter(start) local c = start return function() c = c + 1 return c end end
local function field(t) return t.x + t.y end
local function fails(x) if x > 15 then error("big") end return x end
local function checked(x) return fails(x) + 1 end
local function spread(a) return a, pair(a) end
-- An error in an inlined callee closes the upvalues its caller's frame opened.
local saved = {}
local function capturing(x)
  local c = x * 10
  saved[1] = function() return c end
  c = fails(x) + c
  return c
end

local function run(n)
  local sum = 0
  local t = { x = 1, y = 2 }
  for i = 1, n do
    sum = sum + mix(i, i * 7)
    local p, q = pair(i)
    local r = pair(i)
    local u, v, w, z = triple(i)
    sum = sum + p + q + r + u + v + w + (z == nil and 100 or 0)
    sum = sum + outer(i) + calls_loop(i % 5)
    local next = counter(i)
    sum = sum + next() + next()
    t.x = i
    sum = sum + field(t)
    local ok, e = pcall(checked, i)
    sum = sum + (ok and e or 1000)
    local all = { spread(i) }
    sum = sum + #all + all[2]
    sum = sum + mix(pair(i))
    pcall(capturing, i)
    sum = sum + pair(i * 3) + triple(i * 5)
    sum = sum + saved[1]()
  end
  return sum
end

print(run(20))
run.__jit = 1
print(run(20), run(20))
-- EXPECT: 16937
-- EXPECT: 16937	16937
