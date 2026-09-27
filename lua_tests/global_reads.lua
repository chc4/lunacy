-- Globals read in loops while their values change type (a number's encoding,
-- or the Lua type), are defined late, or are set by a call the loop makes.

local function sum_g(n)
  local s = 0
  for i = 1, n do s = s + g end
  return s
end

local function count_up(n)
  for i = 1, n do counter = counter + i end
  return counter
end

local function set_g(v) g = v end
local function set_by_callee(n)
  local s = 0
  for i = 1, n do
    s = s + g
    if i == 3 then set_g(100) end
  end
  return s
end

local function kinds(n)
  local out = {}
  for i = 1, n do
    out[i] = type(v)
    if i == 1 then v = "s" elseif i == 2 then v = {} elseif i == 3 then v = nil else v = 1.5 end
  end
  local joined = table.concat(out, " ")
  return joined
end

local function late(n)
  local s = 0
  for i = 1, n do
    if undefined_yet then s = s + undefined_yet end
    if i == 2 then undefined_yet = 10 end
  end
  return s
end

local function run()
  g = 1
  print(sum_g(5))
  g = 2.5
  print(sum_g(4))
  g = 3
  print(sum_g(3))
  counter = 0
  print(count_up(10))
  counter = 0.5
  print(count_up(10))
  counter = 2147483000
  print(count_up(100))
  g = 1
  print(set_by_callee(5))
  v = 1
  print(kinds(5))
  undefined_yet = nil
  print(late(4))
end

run()
sum_g.__jit = 1
count_up.__jit = 1
set_by_callee.__jit = 1
kinds.__jit = 1
late.__jit = 1
run()
-- EXPECT: 5
-- EXPECT: 10
-- EXPECT: 9
-- EXPECT: 55
-- EXPECT: 55.5
-- EXPECT: 2147488050
-- EXPECT: 203
-- EXPECT: number string table nil number
-- EXPECT: 20
-- EXPECT: 5
-- EXPECT: 10
-- EXPECT: 9
-- EXPECT: 55
-- EXPECT: 55.5
-- EXPECT: 2147488050
-- EXPECT: 203
-- EXPECT: number string table nil number
-- EXPECT: 20
