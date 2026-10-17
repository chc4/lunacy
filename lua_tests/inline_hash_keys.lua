-- Small functions inlined into a loop that reads fields of tables: a function
-- reading and writing fields of a table its caller passed it and reads itself,
-- one changing a field's type and adding a key, one given another table in
-- place of its parameter, and a table of the caller's it isn't passed, whose
-- fields the caller reads around each call. What's read decides what's summed.
-- Once, and in loops run often enough for JIT code.

local function bump(m) m.count = m.count + m.step return m.count end
local function retype(m, k) if k % 50 == 0 then m.step = m.step + 0.5 end m.extra = k return m.step end
local function swap(m, other) m = other m.count = m.count + 1 return m.count end

local function run(n)
  local m = { count = 0, step = 1 }
  local o = { count = 100, step = 3 }
  local side = { a = 1, b = 2 }
  local total = 0
  for k = 1, n do
    total = total + side.a + m.count
    total = total + bump(m) + side.b
    total = total + retype(m, k) + m.step + (m.extra or 0)
    total = total + swap(m, o) + m.count + o.count + side.a
    side.a = side.a + 1
  end
  return total
end

print(run(3))
print(run(500))
-- EXPECT: 657
-- EXPECT: 1640697.5
