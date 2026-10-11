-- Stores into array parts the peephole holds, and loads of what they store,
-- through tables that may be one another: each loop runs often enough for JIT
-- code, and reads back what it stored, through the same table, another local
-- holding it, or another table, at constant and register keys.

local n = 600

-- Stored then loaded, the same element: the load is the stored value.
local function same(t)
  local s = 0
  for i = 1, n do
    t[1] = i
    s = s + t[1]
    t[1] = i * 2
    t[2] = i
    s = s + t[1] + t[2]
  end
  return s
end

-- Through two locals: one table, or two, the loads seeing whichever store
-- was last into their element.
local function aliased(t, u)
  local s = 0
  for i = 1, n do
    t[1] = i
    u[1] = i + 1
    s = s + t[1]
    u[2] = 3
    t[2] = 5
    s = s + u[2] * 7 + t[2]
  end
  return s
end

-- At a key in a register, which may be another constant's element.
local function keyed(t)
  local s = 0
  for i = 1, n do
    local k = i % 3 + 1
    t[1] = i
    t[k] = 10
    s = s + t[1] + t[k]
  end
  return s
end

-- A store of nil between two loads of the same element: the array part may be
-- shorter after it, and the second load finds the element as it is then.
local function shortened(t)
  local s = 0
  for i = 1, n do
    t[2] = i
    s = s + t[2]
    t[3] = nil
    s = s + (t[2] or 0)
    t[3] = 1
  end
  return s, #t
end

local t = { 0, 0, 0 }
print(same({ 0, 0 }), aliased(t, t), aliased({ 0, 0 }, { 0, 0 }), keyed({ 0, 0, 0 }))
print(shortened({ 0, 0, 0 }))
-- EXPECT: 721200	204900	195900	128000
-- EXPECT: 360600	3
