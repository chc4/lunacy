-- A value computed before a jump that is an instruction's only way on, and before a branch: a loop
-- whose body computes a value, replaces it on one way of a branch, and sums it.

local function run(n, low)
  local sum = 0
  for i = 1, n do
    local x = (i % 7) - 3
    if i == n then
      x = low
    end
    sum = sum + x
  end
  return sum
end

print(run(10, 100))
print(run(1000, 100))
-- EXPECT: 97
-- EXPECT: 100
