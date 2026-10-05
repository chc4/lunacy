-- Userdata from newproxy: its type, equality by identity, as a table key, and
-- in an array part, of one kind and mixed, which the specializer guards. A
-- proxy may share another's metatable. Run interpreted, then with the
-- functions JIT compiled.
local a, b = newproxy(), newproxy(true)
local c = newproxy(b)
local keys = {}
keys[a] = 1; keys[b] = 2; keys[c] = 3
local list = {a, b, c}
local mixed = {a, 1, b, "x"}
local function count(t, u)
  local n = 0
  for i = 1, #t do
    if t[i] == u then n = n + 1 end
  end
  return n
end
local function kinds(t)
  local n = 0
  for i = 1, #t do
    if type(t[i]) == "userdata" then n = n + 1 end
  end
  return n
end
local function run()
  print(type(a), type(b), type(c))
  print(a == a, a == b, b == c, a ~= c)
  print(keys[a], keys[b], keys[c], keys[newproxy()])
  print(count(list, a), count(list, newproxy()), kinds(list))
  print(count(mixed, b), kinds(mixed))
  list[#list + 1] = newproxy(c)
  print(#list, kinds(list))
end
run()
count.__jit = 1
kinds.__jit = 1
run()
-- EXPECT: userdata	userdata	userdata
-- EXPECT: true	false	false	true
-- EXPECT: 1	2	3	nil
-- EXPECT: 1	0	3
-- EXPECT: 1	2
-- EXPECT: 4	4
-- EXPECT: userdata	userdata	userdata
-- EXPECT: true	false	false	true
-- EXPECT: 1	2	3	nil
-- EXPECT: 1	0	4
-- EXPECT: 1	2
-- EXPECT: 5	5
