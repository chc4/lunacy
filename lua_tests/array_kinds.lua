-- Array kinds: loops reading an array of one kind; one whose kind changes
-- partway through the loop by a store through another name, by table.insert,
-- and by emptying it and refilling it; elements swapped within their array,
-- and one stored into another; arrays mixed from the start, of integers
-- and doubles, with a nil hole; nested arrays; and constructors. Each read
-- value's type decides what the loop does with it, so a read typed with a kind
-- the array no longer has would go wrong. Once, and in a loop run often enough
-- for JIT code.

local function classify(t, n)
  local ints, strs, others = 0, 0, 0
  for i = 1, n do
    local v = t[i]
    if v == "s" then
      strs = strs + 1
    elseif v ~= nil and v == v + 0 then
      ints = ints + v
    else
      others = others + 1
    end
  end
  return ints .. "/" .. strs .. "/" .. others
end

local function changes(n)
  local t = {}
  for i = 1, n do t[i] = i end
  local u = t
  local sum, strs = 0, 0
  for i = 1, n do
    local v = t[i]
    if v ~= "s" then sum = sum + v else strs = strs + 1 end
    if i == 3 then u[n] = "s" end
  end
  return sum .. "/" .. strs
end

local function nested(n)
  local grid = {}
  for i = 1, n do
    local row = {}
    for j = 1, n do row[j] = i * j end
    grid[i] = row
  end
  grid[2][2] = "s"
  local total, strs = 0, 0
  for i = 1, n do
    for j = 1, n do
      local v = grid[i][j]
      if v == "s" then strs = strs + 1 else total = total + v end
    end
  end
  return total .. "/" .. strs
end

local function swaps(n)
  local t, s = {}, {}
  for i = 1, n do t[i] = i end
  for i = 1, n do s[i] = "s" end
  for i = 1, n - 1 do t[i], t[i + 1] = t[i + 1], t[i] end
  s[1] = t[1]
  return classify(t, n) .. "," .. classify(s, n)
end

local function run(n)
  local out = {}
  local ints = {}
  for i = 1, n do ints[i] = i end
  out[#out + 1] = classify(ints, n)
  out[#out + 1] = changes(n)
  out[#out + 1] = classify({1, "s", 2, "s", 3}, 5)
  out[#out + 1] = classify({1, 2.5, 3, 4.5}, 4)
  local holes = {}
  holes[1] = 1
  holes[3] = 3
  out[#out + 1] = classify(holes, 3)
  local grow = {1, 2, 3}
  table.insert(grow, "s")
  out[#out + 1] = classify(grow, 4)
  local refill = {}
  for i = 1, n do refill[i] = i end
  out[#out + 1] = classify(refill, n)
  for i = 1, n do refill[i] = nil end
  for i = 1, n do refill[i] = "s" end
  out[#out + 1] = classify(refill, n)
  out[#out + 1] = nested(4)
  out[#out + 1] = swaps(n)
  local joined = table.concat(out, " ")
  return joined
end

local first = run(8)
local same = true
for i = 1, 300 do
  if run(8) ~= first then same = false end
end
print(first)
print(run(3))
print(same)
-- EXPECT: 36/0/0 28/1 6/2/0 11/0/0 4/0/1 6/1/0 36/0/0 0/8/0 96/1 36/0/0,2/7/0
-- EXPECT: 6/0/0 6/0 6/2/0 11/0/0 4/0/1 6/1/0 6/0/0 0/3/0 96/1 6/0/0,2/2/0
-- EXPECT: true
