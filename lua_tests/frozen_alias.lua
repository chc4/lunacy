-- A load from a frozen table is of no element a store held in the peephole
-- writes: a store into the frozen table trips first. A loop holds a store,
-- loads from a frozen table, and loads the stored element again; then a store
-- into the frozen table through another name, seen by the next load.

local frozen = jit and jit.frozen or function(t) return t end

local function run(n)
  local lookup = { 10, 20, 30, 40 }
  local t = frozen(lookup)
  local s = { 0, 0 }
  local sum = 0
  for i = 1, n do
    s[1] = i
    local v = t[i % 4 + 1]
    sum = sum + v + s[1]
    if i == math.floor(n / 2) then
      lookup[2] = 200
    end
  end
  return sum
end

print(run(10))
print(run(2000))
-- EXPECT: 485
-- EXPECT: 2096000
