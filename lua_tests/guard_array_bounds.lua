-- Integer keys read and write a table's array part behind a dynamic test that
-- the key is in it (Note [Dynamic guards]); a key that isn't goes through the
-- hash part. Each loop runs keys in the array part until it's compiled, then
-- keys outside it: past its end, zero and negative. Keys stay small: arrays
-- aren't sparse, so a huge key would allocate its whole array part.

-- Reads with a register key, running off the end.
local function read_past(n)
  local t = {}
  for i = 1, 20 do t[i] = i * 2 end
  local sum, nils = 0, 0
  for i = 1, n do
    local v = t[i]
    if v == nil then nils = nils + 1 else sum = sum + v end
  end
  return sum, nils
end
print(read_past(60))

-- Zero and negative keys live in the hash part.
local function below_one()
  local t = {10, 20, 30}
  t[0] = 5
  t[-1] = 7
  local sum = 0
  for i = -1, 3 do sum = sum + t[i] end
  for i = 1, 50 do sum = sum + t[(i % 5) - 1] end
  return sum
end
print(below_one())

-- Writes with a register key: in the array part, then past it and back.
local function write_past(n)
  local t = {0, 0, 0, 0, 0, 0, 0, 0}
  for i = 1, n do
    local k = (i % 12) + 1
    local v = t[k]
    if v == nil then v = 0 end
    t[k] = v + i
  end
  local sum = 0
  for k = 1, 12 do
    local v = t[k]
    if v ~= nil then sum = sum + v end
  end
  return sum, #t
end
print(write_past(120))

-- Constant keys: t[3] on tables of different lengths.
local function const_keys(tables)
  local sum, nils = 0, 0
  for round = 1, 20 do
    for j = 1, #tables do
      local t = tables[j]
      local v = t[3]
      if v == nil then nils = nils + 1 else sum = sum + v end
      t[5] = round
    end
  end
  return sum, nils
end
print(const_keys({{1, 2, 3, 4}, {1, 2}, {}, {9, 9, 9}}))

-- Appending grows the array part while the loop runs.
local function append(n)
  local t = {}
  for i = 1, n do
    t[#t + 1] = i
  end
  local sum = 0
  for i = 1, n + 5 do
    local v = t[i]
    if v ~= nil then sum = sum + v end
  end
  return #t, sum
end
print(append(300))

-- Keys well past the end, in the hash part, then read back.
local function scattered(n)
  local t = {1, 2, 3}
  for i = 1, n do t[i * 10] = i end
  local sum = 0
  for i = 1, n * 10 do
    local v = t[i]
    if v ~= nil then sum = sum + v end
  end
  return sum
end
print(scattered(40))
-- EXPECT: 420	40
-- EXPECT: 792
-- EXPECT: 7260	12
-- EXPECT: 240	40
-- EXPECT: 300	45150
-- EXPECT: 826
