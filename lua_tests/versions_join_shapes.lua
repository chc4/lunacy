-- A loop header reached in more contexts than MAX_VERSIONS gets a version for
-- their join (Note [Version compatibility]). Here the header's contexts differ
-- in a local's type and in which fields of a shaped table are known, so the
-- join forgets the shapes and hash keys, and must still accept the jumps that
-- keep them.
local function walk(t, values)
  local acc = 0
  local v = 0
  for i = 1, #values do
    local x = values[i]
    local kind = i % 7
    if kind == 0 then
      v = x + 1
      acc = acc + t.a
    elseif kind == 1 then
      v = x * 0.5
      acc = acc + t.b
    elseif kind == 2 then
      v = "s" .. x
      acc = acc + t.a + t.c
    elseif kind == 3 then
      v = { n = x }
      acc = acc + v.n + t.d
    elseif kind == 4 then
      v = x > 10
      acc = acc + t.b + t.d
    elseif kind == 5 then
      v = nil
      acc = acc + t.c
    else
      v = walk
      acc = acc + t.e
    end
  end
  return acc, type(v)
end

local values = {}
for i = 1, 300 do values[i] = i end
local t = { a = 1, b = 2, c = 3, d = 4, e = 5 }
for round = 1, 3 do
  print(walk(t, values))
end

-- The same shaped table under several local layouts at one loop header.
local function fields(tables, n)
  local sum = 0
  for i = 1, n do
    local t = tables[(i % #tables) + 1]
    local w = t.w
    if i % 2 == 0 then
      sum = sum + w + t.h
    elseif i % 3 == 0 then
      sum = sum + t.h * 2
    else
      local s = t.w .. ""
      sum = sum + #s
    end
    if i % 5 == 0 and t.x ~= nil then sum = sum + t.x end
  end
  return sum
end
print(fields({ { w = 3, h = 4 }, { w = 1.5, h = 2 }, { w = 7, h = 8, x = 1 } }, 400))
-- EXPECT: 7524	function
-- EXPECT: 7524	function
-- EXPECT: 7524	function
-- EXPECT: 2531.5
