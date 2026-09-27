-- A return is in two halves (Note [Returns]): the callee moves its B - 1
-- results, or all up to the top, down to the function's slot, and the caller's
-- `Arrive` pads them with nil to its C - 1, or takes all. Each count of results
-- meets each count wanted, in the interpreter and, run often, in JIT code; and a
-- call site with more functions than it specializes calls natives and Lua
-- functions alike through a generic call, where a native skips the `Arrive`.
-- (No `return f(x)`: that is a tail call. No `...`: VARARG.)

local function none() end
local function one() return 1 end
local function two() return 1, 2 end
local function three() return 1, 2, 3 end
-- 0 and every result of `f`: a return up to the top (B = 0).
local function all(f) return 0, f() end
-- Its arguments, taking up to three from a call up to the top (B = 0).
local function show(a, b, c) return tostring(a) .. ' ' .. tostring(b) .. ' ' .. tostring(c) end

local fs = { none, one, two, three }
local function wants(f)
  local a = f()
  local b, c = f()
  local d, e, g = f()
  f()
  return show(a), show(b, c), show(d, e, g), show(f()), #{f()}
end

for i = 1, #fs do print(wants(fs[i])) end
print(show(all(two)), show(all(none)), #{all(three)}, type(all(one)), tostring(two()))

-- Hot, with a local declared after each call over the results' slots.
local function num(x)
  if x == nil then return 0 end
  return x
end
local sum = 0
for i = 1, 300 do
  for j = 1, #fs do
    local a, b, c, d = fs[j]()
    local x
    sum = sum + num(a) + num(b) + num(c) + num(d) + num(x)
    local p, q, r, s = all(fs[j])
    sum = sum + p + num(q) + num(r) + num(s) + #{all(fs[j])}
  end
end
print(sum)

-- One site, more functions than it specializes: natives and Lua functions.
local callees = { none, one, math.abs, two, tostring, three, math.floor, show }
local out = {}
for i = 1, 200 do
  local f = callees[i % #callees + 1]
  local a, b = f(-i)
  out[#out + 1] = tostring(a) .. ',' .. tostring(b)
end
print(out[1], out[2], out[3], out[4], out[5], out[6], out[7], out[8], #out)

-- A native returning fewer results than wanted: the rest are nil, where the
-- call's function and arguments were.
local p, q, r = math.abs(-5)
print(p, q, r)
local stale = 0
for i = 1, 300 do
  local a, b, c = math.floor(-i)
  if b ~= nil or c ~= nil then stale = stale + 1 end
end
print(stale)
-- EXPECT: nil nil nil	nil nil nil	nil nil nil	nil nil nil	0
-- EXPECT: 1 nil nil	1 nil nil	1 nil nil	1 nil nil	1
-- EXPECT: 1 nil nil	1 2 nil	1 2 nil	1 2 nil	2
-- EXPECT: 1 nil nil	1 2 nil	1 2 3	1 2 3	3
-- EXPECT: 0 1 2	0 nil nil	4	number	1
-- EXPECT: 9000
-- EXPECT: 1,nil	2,nil	1,2	-4,nil	1,2	-6,nil	-7 nil nil,nil	nil,nil	200
-- EXPECT: 5	nil	nil
-- EXPECT: 0
