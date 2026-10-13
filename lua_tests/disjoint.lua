-- Elements of tables jit.disjoint knows are different tables are different
-- elements: a loop holds a store into one past a load from another. A table
-- that reaches a later disjoint site through a name the context doesn't
-- connect to it is checked against the tables already known different, and a
-- table passed twice is not different from itself. The tables are fields
-- jit.learn learns, so the loads know the arrays' kinds.

local disjoint = jit and jit.disjoint or function() end
local learn = jit and jit.learn or function(t) return t end

local function run(n, m)
  learn(m)
  local a, b = m.a, m.b
  disjoint(a, b)
  local c = m.c
  disjoint(c)
  local sum = 0
  for i = 1, n do
    a[1] = i
    local v = c[1] + b[i % 2 + 1]
    a[1] = v
    sum = sum + a[1] + c[2]
  end
  return sum
end

local t, u, w = { 0, 0 }, { 5, 7 }, { 3, 4 }
print(run(10, { a = t, b = u, c = w }))
print(run(2000, { a = t, b = u, c = w }))
print(run(2000, { a = t, b = u, c = t }))
print(run(2000, { a = t, b = u, c = u }))
print(run(2000, { a = t, b = t, c = u }))
-- EXPECT: 130
-- EXPECT: 26000
-- EXPECT: 2013000
-- EXPECT: 36000
-- EXPECT: 1025000
