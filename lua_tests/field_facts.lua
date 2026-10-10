-- A table kept in a field of an object and passed to small functions inlined
-- into a loop, which learn its array part's kind: what is known of it holds
-- until the field changes. The field is set to an array of another kind made
-- before the loop, so no store into an array part tells, directly and through
-- another reference to the object; and another object's field of the same
-- name is set. What's read decides what's summed. Once, and in loops run
-- often enough for JIT code.

local function first(s) return s[1] + s[2] end

local function run(n)
  -- Integers from a loop's index, an array of the integer kind; constants are
  -- doubles.
  local ints, doubles, others = {}, { 1.5, 2.25, 3.5 }, {}
  for j = 1, 3 do ints[j], others[j] = j, j + 3 end
  local m = { stack = ints }
  local alias = m
  local o = { stack = ints }
  local total = 0
  for i = 1, n do
    local s = m.stack
    total = total + first(s) + s[3]
    if i % 7 == 0 then m.stack = doubles end
    if i % 11 == 0 then alias.stack = ints end
    if i % 13 == 0 then o.stack = doubles end
    s = m.stack
    total = total + first(s) + s[3]
    if i % 5 == 0 then m.stack = others end
    if i % 3 == 0 then m.stack = ints end
  end
  return total
end

print(run(4))
print(run(500))
-- EXPECT: 48
-- EXPECT: 7635
