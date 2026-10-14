-- A field of the caller's table an inlined callee retypes through its parameter, which
-- holds the table the caller's own register does: the caller's hash key comes back with
-- the type the callee left, as the store moved the witness to the table's new epoch.
local function bump(m) m.count = m.count + m.step return m.count end
local function retype(m, k) if k % 50 == 0 then m.step = m.step + 0.5 end return m.step end

local function run(n)
  local m = { count = 0, step = 1 }
  m.count = n - n
  m.step = n - n + 1
  local total = 0
  for k = 1, n do
    total = total + bump(m)
    total = total + retype(m, k)
  end
  return total
end

print(run(3))
print(run(500))
-- EXPECT: 9
-- EXPECT: 305567.5
