-- A value stored into an array part known to hold integers is narrowed by its
-- value: a whole double, computed from doubles (a division) or read from an
-- array of doubles, keeps the array of integers; a double that isn't whole, a
-- string, and a value of unknown type stored the same way are stored as they
-- are. What's read back decides what's done with it. Once, and in loops run
-- often enough for JIT code.

local halves = {}
for i = 1, 16 do halves[i] = i / 2 end

local function run(n, odd)
  local total = 0
  for k = 1, n do
    local s = {}
    for i = 1, 16 do s[i] = i end
    for i = 1, 16 do
      local v = s[i]
      s[i] = v + halves[i] * 2 - v
      total = total + s[i]
    end
    s[3] = s[1] + (k % 2) / 2
    total = total + s[3] * 2
    if odd then
      s[5] = "x"
      total = total + #s[5]
    end
  end
  return total
end

print(run(1, false))
print(run(300, false))
print(run(300, true))
-- EXPECT: 139
-- EXPECT: 41550
-- EXPECT: 41850
