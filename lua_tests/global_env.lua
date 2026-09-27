-- Globals written and read through aliases of the environment: `_G`, a local
-- holding it, and a table parameter that is it. Also `_G = t`, which must not
-- change where globals live.

local function via_g(n)
  for i = 1, n do
    x = i
    _G.x = _G.x + 1
  end
  return x
end

local env = _G
local function via_local(n)
  local s = 0
  for i = 1, n do
    y = i
    s = s + env.y
    env.y = 10
    s = s + y
  end
  return s
end

local function store_through(u, n)
  local s = 0
  for i = 1, n do
    s = s + w
    u.w = i * 100
  end
  return s
end

local function set_field(u, v) u.w = v end
local function store_in_callee(u, n)
  local s = 0
  for i = 1, n do
    s = s + w
    set_field(u, i * 1000)
  end
  return s
end

local t = {}
local function rebound(n)
  local s = 0
  for i = 1, n do
    z = i
    _G.z = i * 10
    s = s + z + _G.z + t.z + env.z
  end
  return s
end

local function run()
  print(via_g(3))
  print(via_local(3))
  w = 1
  print(store_through(_G, 3), w)
  print(store_through({}, 3), w)
  w = 1
  print(store_in_callee(_G, 3), w)
  print(store_in_callee({}, 3), w)
  _G = t
  print(rebound(2))
  env._G = env
  print(z, t.z, env.z)
  t.z = nil
end

run()
via_g.__jit = 1
via_local.__jit = 1
store_through.__jit = 1
store_in_callee.__jit = 1
rebound.__jit = 1
run()
-- EXPECT: 4
-- EXPECT: 36
-- EXPECT: 301	300
-- EXPECT: 900	300
-- EXPECT: 3001	3000
-- EXPECT: 9000	3000
-- EXPECT: 66
-- EXPECT: 2	20	2
-- EXPECT: 4
-- EXPECT: 36
-- EXPECT: 301	300
-- EXPECT: 900	300
-- EXPECT: 3001	3000
-- EXPECT: 9000	3000
-- EXPECT: 66
-- EXPECT: 2	20	2
