-- Booleans as values: table constructors of them, `and` chains over them,
-- passed as arguments and returned, and tested by `if` (TEST) against
-- nil, false and other values, as queens uses them. Run interpreted, then
-- with the functions JIT compiled.
local function n(b) if b then return 1 end return 0 end
local t = {true, true, false}
local function g(i, j) return t[i] and t[j] end
local function h(x) if x then return true end return false end
local function set(i, v) t[i] = v end
local function run()
  print(n(true), n(false), n(nil), n(1))
  print(n(g(1, 2)), n(g(1, 3)), n(g(3, 1)))
  print(n(h(1)), n(h(nil)))
  local r = true
  for i = 1, 3 do r = r and h(i) end
  print(n(r))
end
run()
n.__jit = 1
g.__jit = 1
h.__jit = 1
run()
set(1, false)
print(n(t[1]), n(g(1, 2)))
print(true, false, h(1), g(2, 3))
-- EXPECT: 1	0	0	1
-- EXPECT: 1	0	0
-- EXPECT: 1	0
-- EXPECT: 1
-- EXPECT: 1	0	0	1
-- EXPECT: 1	0	0
-- EXPECT: 1	0
-- EXPECT: 1
-- EXPECT: 0	0
-- EXPECT: true	false	true	false
