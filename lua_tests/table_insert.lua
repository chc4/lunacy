-- table.insert follows Lua 5.1's `tinsert`: a position from 1 to #t + 1
-- moves the elements from it up one, one past the end stores there and moves
-- nothing, and one below 1 moves every element up one, down to the position
-- (zero and negative keys live in the hash part). Where that leaves holes,
-- the length may be any border, so only the elements are printed.

local function show(t, lo, hi)
  local parts = {}
  for i = lo, hi do parts[#parts + 1] = tostring(t[i]) end
  return table.concat(parts, " ")
end

local t = {10, 20, 30}
table.insert(t, 40)
table.insert(t, 1, 5)
table.insert(t, 3, 15)
print(#t, show(t, 1, 6))

local past = {1, 2}
table.insert(past, 5, "x")
print(show(past, 1, 6))

local zero = {1, 2, 3}
table.insert(zero, 0, "z")
print(show(zero, -1, 5))

local negative = {1, 2}
table.insert(negative, -2, "n")
print(show(negative, -3, 4))

local nils = {1, 2}
table.insert(nils, nil)
table.insert(nils, 3, nil)
table.insert(nils, 1, nil)
print(#nils, show(nils, 1, 4))

-- In a loop long enough to be compiled.
local q = {}
for i = 1, 100 do
  table.insert(q, 1, i)
  if #q > 10 then table.remove(q) end
end
print(#q, q[1], q[10])
-- EXPECT: 6	5 10 15 20 30 40
-- EXPECT: 1 2 nil nil x nil
-- EXPECT: nil z nil 1 2 3 nil
-- EXPECT: nil n nil nil nil 1 2 nil
-- EXPECT: 3	nil 1 2 nil
-- EXPECT: 10	100	91
