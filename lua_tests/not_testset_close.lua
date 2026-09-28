-- `not`; `or` and `and` into a local other than their operand (TESTSET), on
-- nil, false, a number, and a bool only known when it runs; a loop body whose
-- local a closure captures, closed each iteration (CLOSE); `table.remove`.
-- Once, and in a loop run often enough for JIT code.

local function run(n)
  local out = {}
  local fns = {}
  for i = 1, 3 do
    local x = i * n
    fns[i] = function() return x end
  end
  out[#out + 1] = fns[1]() + fns[2]() + fns[3]()

  local none, no, five = nil, false, 5
  local big = n > 2
  out[#out + 1] = tostring(not none) .. tostring(not no) .. tostring(not five) .. tostring(not big)
  local a = none or five
  local b = no or none
  local c = five and "and"
  local d = none and five
  local e = big or 7
  local f = big and 8
  local g = (not big) or 9
  local h = (not big) and 10
  out[#out + 1] = tostring(a) .. tostring(b) .. tostring(c) .. tostring(d)
  out[#out + 1] = tostring(e) .. tostring(f) .. tostring(g) .. tostring(h)

  local t = {1, 2, 3, 4}
  local last = table.remove(t)
  local first = table.remove(t, 1)
  local empty = table.remove({})
  out[#out + 1] = last .. first .. #t .. t[1] .. t[2] .. tostring(empty)
  return out
end

local first = {run(1), run(3)}
local same = 0
for i = 1, 300 do
  local again = {run(1), run(3)}
  for r = 1, 2 do
    for k = 1, #first[r] do
      if again[r][k] == first[r][k] then same = same + 1 end
    end
  end
end
for r = 1, 2 do
  for k = 1, #first[r] do print(first[r][k]) end
end
print(same == 300 * (#first[1] + #first[2]))
-- EXPECT: 6
-- EXPECT: truetruefalsetrue
-- EXPECT: 5nilandnil
-- EXPECT: 7falsetrue10
-- EXPECT: 41223nil
-- EXPECT: 18
-- EXPECT: truetruefalsefalse
-- EXPECT: 5nilandnil
-- EXPECT: true89false
-- EXPECT: 41223nil
-- EXPECT: true
