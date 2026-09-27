-- A field read before and after a call that inserts keys into its table, which
-- moves the table's entries: after the call the field must be found again, not
-- read through the old address.
local function grow(t, from)
  for i = from, from + 20 do t["k" .. i] = i end
end

local function read_around(t, n)
  local s = 0
  for i = 1, n do
    s = s + t.a
    grow(t, i * 100)
    s = s + t.a
    t.a = t.a + 1
  end
  return s
end

local function run()
  -- The table's field read afresh too, which a store through a stale witness
  -- would have missed.
  local t = { a = 1 }
  print(read_around(t, 4), t.a)
  local u = { a = 0.5 }
  print(read_around(u, 3), u.a)
end

run()
read_around.__jit = 1
grow.__jit = 1
run()
-- EXPECT: 20	5
-- EXPECT: 9	3.5
-- EXPECT: 20	5
-- EXPECT: 9	3.5
