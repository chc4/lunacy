-- Owned strings are built in one allocation sized from their operands (Note
-- [String cells]): concatenations of several operands, numbers among them, and
-- strings grown a byte at a time must come out whole, work as table keys, and
-- survive collections while referenced.
local function row(n)
  local out = ""
  for i = 1, n do
    out = out .. ((i % 3 == 0) and "O" or "-")
  end
  return out
end

local kept = {}
for i = 1, 200 do
  kept[i] = row(i) .. "|" .. i .. "|" .. "end"
  if i % 50 == 0 then collectgarbage("collect") end
end
print(#kept[1], kept[1])
print(#kept[200], string.sub(kept[200], 1, 12), string.sub(kept[200], -8))

local total = 0
for i = 1, 200 do total = total + #kept[i] end
print(total)

-- Built keys find the entries built alike.
local t = {}
for i = 1, 20 do t["k" .. i .. "_" .. i * 2] = i end
local found = 0
for i = 1, 20 do found = found + t["k" .. i .. "_" .. i * 2] end
print(found)

-- A string's bytes count towards the heap, and are freed with it.
kept = nil
collectgarbage("collect")
local base = collectgarbage("count")
local big = {}
for i = 1, 100 do big[i] = row(2000) .. i end
local grown = collectgarbage("count") - base
big = nil
collectgarbage("collect")
local freed = collectgarbage("count") - base
print(grown > 150, freed < 20)
-- EXPECT: 7	-|1|end
-- EXPECT: 208	--O--O--O--O	|200|end
-- EXPECT: 21592
-- EXPECT: 210
-- EXPECT: true	true
