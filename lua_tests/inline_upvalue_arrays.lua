-- An inlined callee loads elements of a table it reaches as an upvalue: one its caller holds in a
-- slot, and one only the callee's closure holds. Each array's kind is tested where the table is
-- reached, and a store of a float into one makes it mixed.
local shared = {}
for i = 1, 40 do shared[i] = i end
local function far(i) return shared[i] end

local function run(n)
  local t = {}
  for i = 1, 40 do t[i] = i * 2 end
  local function near(i) return t[i] end
  local s = 0
  for _ = 1, n do
    for i = 1, 40 do s = s + near(i) + far(i) end
  end
  t[3], shared[5] = 0.5, 0.25
  for i = 1, 40 do s = s + near(i) + far(i) end
  return s
end

print(run(5))
print(run(50))
run.__jit = 1
print(run(50))
-- EXPECT: 14749.75
-- EXPECT: 125212.25
-- EXPECT: 125212.25
