-- The kind of a table's array part an upvalue holds, which loads of the upvalue
-- keep: read in loops through the upvalue, with the array's kind changed by a
-- store through another name partway, the upvalue set to a table of another
-- kind, and through an inlined helper reading its own upvalue's table. Each
-- read value's type decides what is done with it, so a read typed with a kind
-- the array no longer has would go wrong. Once, and in loops run often enough
-- for JIT code.

local function classify(v)
  if type(v) == "number" then return v end
  if type(v) == "string" then return 1000 end
  return 100000
end

local function machine(n)
  local data = {}
  for i = 1, n do data[i] = i end
  local alias = data
  local function sum()
    local s = 0
    for i = 1, n do s = s + classify(data[i]) end
    return s
  end
  local function widen(i, v) alias[i] = v end
  local function replace(t) data = t end
  return sum, widen, replace
end

local function run(n)
  local sum, widen, replace = machine(n)
  local a = sum()
  widen(2, "s")
  local b = sum()
  local strings = {}
  for i = 1, n do strings[i] = "x" end
  replace(strings)
  local c = sum()
  widen(3, true)
  local d = sum()
  return a, b, c, d
end

-- A helper whose own upvalue holds the table, called from a loop.
local function reader(t)
  local function at(i) return t[i] end
  return at
end

local function through(n)
  local t = {}
  for i = 1, n do t[i] = i * 2 end
  local at = reader(t)
  local s = 0
  for i = 1, n do s = s + at(i) end
  t[1] = "s"
  local strings = 0
  for i = 1, n do
    local v = at(i)
    if type(v) == "string" then strings = strings + 1 else s = s + v end
  end
  return s, strings
end

print(run(10))
print(run(500))
print(through(10))
print(through(500))
-- EXPECT: 55	1053	10000	10000
-- EXPECT: 125250	126248	500000	500000
-- EXPECT: 218	1
-- EXPECT: 500998	1
