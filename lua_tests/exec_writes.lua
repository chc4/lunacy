-- A table store done the generic way (appending past the array part, a new
-- hash key) writes no register: a constant loaded before it is still that
-- constant after, and stored narrowed as an integer into another table. A
-- store into a register's table then overwriting the register leaves nothing
-- known of the old value. What's read decides what's done with it. Once, and
-- in loops run often enough for JIT code.

local function weigh(v)
  if math.type then return v end
  if v == math.floor(v) then return v end
  return 1000
end

local function run(n)
  local total = 0
  for k = 1, n do
    local a, b, h = {}, {}, {}
    for i = 0, 40 do
      a[i], b[i] = 0, 0
      h["k" .. i] = 3
    end
    for i = 0, 40 do total = total + weigh(a[i]) + weigh(b[i]) + h["k" .. i] end
    local c = 5
    h.x = c
    c = c / 2
    b[1] = c
    total = total + b[1] * 2 + h.x
  end
  return total
end

print(run(1))
print(run(300))
-- EXPECT: 133
-- EXPECT: 39900
