-- Array kinds learned by a test of an element's truthiness, whose targets are
-- found before the element's guard learns the array's kind: over an array of
-- one kind, and one mixed partway through. Once, and in a loop run often enough
-- for JIT code.

local function count(t, n)
  local c = 0
  for i = 1, n do
    local v = t[i]
    if v then c = c + 1 end
  end
  return c
end

local function run(n)
  local t = {}
  for i = 1, n do t[i] = true end
  local all = count(t, n)
  t[2] = false
  local some = count(t, n)
  return all .. "/" .. some
end

local first = run(8)
local same = true
for i = 1, 300 do
  if run(8) ~= first then same = false end
end
print(first)
print(run(3))
print(same)
-- EXPECT: 8/7
-- EXPECT: 3/2
-- EXPECT: true
