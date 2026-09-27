-- Global functions called in loops and redefined between and during them: Lua
-- to Lua, Lua to a native and back, and the natives `print` and `tostring`
-- themselves overridden.
local bit = require("bit")

local function apply(n)
  local s = 0
  for i = 1, n do s = s + f(i) end
  return s
end

local function redefine_midway(n)
  local s = 0
  for i = 1, n do
    s = s + f(i)
    if i == 2 then f = function(x) return x * 100 end end
  end
  return s
end

local function shout(n)
  for i = 1, n do print("line", i) end
end

local function strings(n)
  local out = {}
  for i = 1, n do out[i] = tostring(i) end
  local joined = table.concat(out, ",")
  return joined
end

local function run()
  f = function(x) return x end
  print(apply(4))
  f = function(x) return x * 2 end
  print(apply(4))
  f = bit.bnot
  print(apply(4))
  f = function(x) return -x end
  print(apply(4))
  f = function(x) return x end
  print(redefine_midway(4))

  local real_print = print
  shout(2)
  print = function(a, b) real_print("wrapped", a, b) end
  shout(2)
  print = real_print
  shout(1)

  local real_tostring = tostring
  print(strings(3))
  tostring = function(x) return "<" .. real_tostring(x) .. ">" end
  -- Printed with tostring restored, as Lua 5.1's print calls the global
  -- tostring, which lunacy's doesn't.
  local wrapped = strings(3)
  tostring = real_tostring
  print(wrapped)
  print(strings(3))
end

run()
apply.__jit = 1
redefine_midway.__jit = 1
shout.__jit = 1
strings.__jit = 1
run()
-- EXPECT: 10
-- EXPECT: 20
-- EXPECT: -14
-- EXPECT: -10
-- EXPECT: 703
-- EXPECT: line	1
-- EXPECT: line	2
-- EXPECT: wrapped	line	1
-- EXPECT: wrapped	line	2
-- EXPECT: line	1
-- EXPECT: 1,2,3
-- EXPECT: <1>,<2>,<3>
-- EXPECT: 1,2,3
-- EXPECT: 10
-- EXPECT: 20
-- EXPECT: -14
-- EXPECT: -10
-- EXPECT: 703
-- EXPECT: line	1
-- EXPECT: line	2
-- EXPECT: wrapped	line	1
-- EXPECT: wrapped	line	2
-- EXPECT: line	1
-- EXPECT: 1,2,3
-- EXPECT: <1>,<2>,<3>
-- EXPECT: 1,2,3
