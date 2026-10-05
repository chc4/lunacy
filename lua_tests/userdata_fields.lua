-- Fields of a userdata, in its metatable's `__index` table (the test runner's
-- `make_userdata` and `userdata_metatable`), read through hash keys: by `.`
-- and by `:`, a missing one nil, two userdata sharing the metatable, and
-- `__index` reassigned between two reads with no call between them. Run
-- interpreted, then with the functions JIT compiled.
local u, v = make_userdata(), make_userdata()
local mt = userdata_metatable
local original = mt.__index
local seven = {answer = function() return 7 end}
local function read(x, n)
  local sum = 0
  for i = 1, n do sum = sum + x.answer() end
  return sum
end
local function method(x, n)
  local sum = 0
  for i = 1, n do sum = sum + x:answer() end
  return sum
end
local function missing(x) return x.nothing end
local function swap(x)
  local before = x.answer
  mt.__index = seven
  local after = x.answer
  mt.__index = original
  return before(), after()
end
local function run()
  print(read(u, 10), read(v, 10), method(u, 10))
  print(missing(u), u.answer == v.answer)
  print(swap(u))
  print(swap(v))
end
run()
read.__jit = 1
method.__jit = 1
missing.__jit = 1
swap.__jit = 1
run()
-- EXPECT: 420	420	420
-- EXPECT: nil	true
-- EXPECT: 42	7
-- EXPECT: 42	7
-- EXPECT: 420	420	420
-- EXPECT: nil	true
-- EXPECT: 42	7
-- EXPECT: 42	7
