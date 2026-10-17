-- Paths learning the same fields of a table in different orders meet: each
-- field's hash key has the same index on every path, so the join keeps them.
-- The fields are read and written after the paths meet. Once, and in loops
-- run often enough for JIT code.

local function run(n)
  local t = { p = 1, q = 2, r = 3 }
  local total = 0
  for i = 1, n do
    if i % 2 == 0 then
      total = total + t.p + t.q + t.r
    else
      total = total + t.r * 2 + t.q + t.p
    end
    total = total + t.p + t.q + t.r
    t.q = t.q + t.p
    t.p = t.r - t.p
  end
  return total, t.p, t.q, t.r
end

print(run(4))
print(run(500))
-- EXPECT: 74	1	8	3
-- EXPECT: 381250	1	752	3
