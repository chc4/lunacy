-- Code a region is entered at inside an inlined call whose frame isn't made, which makes it
-- for a call and returns from it: the code after takes back the base of the frame made, not
-- the one the region was entered with. See Note [Inlined frames].
local function new(n, whole)
  local t = { last = 1, items = {} }
  if whole then t.last = n + 0 end
  return t
end

local function fill(t, k)
  for i = 1, k do
    t.items[t.last] = i * 2
    t.last = t.last + 1
  end
end

local function sum(t)
  local s = 0
  for i = 1, t.last - 1 do
    s = s + (t.items[i] or 0)
  end
  return s, t.last
end

local function run()
  local total, lasts = 0, 0
  for j = 1, 20 do
    local t = new(1, j % 2 == 0)
    fill(t, j)
    local s, last = sum(t)
    total, lasts = total + s, lasts + last
  end
  return total, lasts
end
for _ = 1, 30 do run() end
print(run())
-- EXPECT: 3080	230
