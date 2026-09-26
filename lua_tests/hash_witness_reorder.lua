-- A field read and written in a loop whose table is cleared and refilled with
-- its keys in another order: the witness's index then holds another key, with
-- a value of the same type, which the field's reads and writes must not take
-- for its own (see Note [Hash witnesses]). The table is printed afterwards, as
-- a write to the wrong key and reads of it can still sum to the right total.
local function reads(t, n)
  local s = 0
  for i = 1, n do
    s = s + t.a
    if i == 5 then
      table.clear(t)
      t.b = 100
      t.a = 1
    end
  end
  return s
end
local t = {}
t.a = 10; t.b = 20
print(reads(t, 10))
print(t.a, t.b)
reads.__jit = 1
t = {}
t.a = 10; t.b = 20
print(reads(t, 10))
print(t.a, t.b)
-- EXPECT: 55
-- EXPECT: 1	100
-- EXPECT: 55
-- EXPECT: 1	100
