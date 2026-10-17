-- More paths than a point has versions for reach it, none of whose contexts
-- another's version accepts, as a local holds another type on each: knowing
-- different sets of a table's fields, one set within another's, so their join
-- knows the fields both know, and the table keeps them. The fields are read
-- after the paths meet and written, so a hash key the join lost or kept
-- wrongly reads the wrong field. Once, and in loops run often enough for JIT
-- code.

local function run(n)
  local t = { a = 1, b = 2, c = 3, d = 4, e = 5 }
  local total = 0
  for i = 1, n do
    local k = i % 5
    local x
    if k == 0 then
      total = total + t.a + t.b
      x = i
    elseif k == 1 then
      total = total + t.b + t.a + t.c
      x = i + 0.5
    elseif k == 2 then
      total = total + t.a + t.d + t.b
      x = "s"
    elseif k == 3 then
      total = total + t.c + t.d + t.a + t.b
      x = true
    else
      total = total + t.a + t.b + t.e
      x = { i }
    end
    total = total + t.a * 2 + t.b
    if type(x) == "number" then total = total + x end
    t.a = t.a + 1
    t.b = t.b + t.a
  end
  return total, t.a, t.b, t.c, t.e
end

print(run(4))
print(run(500))
-- EXPECT: 98.5	5	16	3	5
-- EXPECT: 42345800	501	125752	3	5
