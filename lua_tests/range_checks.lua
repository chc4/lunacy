-- Integer ops whose operands' ranges keep their results integers, unchecked;
-- ones near the integer's limit, whose results may not be, checked. In-array
-- tests of keys within what an earlier test found the array part to be, and
-- the array part then shrunk by a nil store and by table.remove, in loops run
-- often enough for JIT code.

local function arith(n)
  local sum = 0
  for i = 1, n do
    local lo = i % 256
    local hi = (i * 7) % 256
    sum = sum + (hi * 256 + lo + 1) % 65536
    local big = (i % 1073741824) * 4 + 1073741000
    sum = sum + big % 1000
  end
  return sum
end

local function lengths(n, shrink)
  local t = {}
  for i = 1, 16 do t[i] = i end
  local sum = 0
  for i = 1, n do
    local last = t[16]
    local k = i % 16 + 1
    sum = sum + (t[k] or 100) + (last or 1000)
    if shrink == "nil" and i == 50 then
      t[16] = nil
    elseif shrink == "remove" and i == 50 then
      table.remove(t)
    end
  end
  return sum
end

print(arith(10) .. " " .. arith(3000))
print(lengths(10, nil) .. " " .. lengths(3000, nil))
print(lengths(3000, "nil") .. " " .. lengths(3000, "remove"))
-- EXPECT: 98845 99776676
-- EXPECT: 225 73476
-- EXPECT: 2991732 2991732
