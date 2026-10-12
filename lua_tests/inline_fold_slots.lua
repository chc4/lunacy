-- Inlined calls whose code folds into their caller's, their frames never made:
-- results of every count into slots the next call's function is moved into,
-- and a constant loaded in a callee whose fact is contracted, rebuilt in the
-- callee's code though its frame is the caller's. Run often enough for JIT code.

local function none() end
local function one() return 1 end
local function two() return 1, 2 end
local function three() return 1, 2, 3 end
local function all(f) return 0, f() end
local fs = { none, one, two, three }
local function num(x)
  if x == nil then return 0 end
  return x
end
local sum = 0
for i = 1, 300 do
  for j = 1, #fs do
    local a, b, c, d = fs[j]()
    local x
    sum = sum + num(a) + num(b) + num(c) + num(d) + num(x)
    local p, q, r, s = all(fs[j])
    sum = sum + p + num(q) + num(r) + num(s) + #{all(fs[j])}
  end
end
print(sum)
-- EXPECT: 9000
