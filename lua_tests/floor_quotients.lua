-- math.floor of an integer's quotient by a positive whole constant: by powers
-- of two and others, of negative integers, with the integer written between
-- the division and the floor, and with the quotient used otherwise too. And a
-- branch that divides where the other doesn't, before they meet: the code
-- after them is the same either way. Once, and in loops run often enough for
-- JIT code.

local floor = math.floor

local function split(v)
  return floor(v / 256), v % 256
end

local function thirds(v)
  return floor(v / 3) + floor(v / 7) * 2
end

local function rewritten(v)
  local q = v / 4
  v = v + 1
  return floor(q) + v
end

local function shared(v)
  local q = v / 8
  return floor(q) + q * 2
end

local function branchy(v)
  local n
  if v % 3 == 0 then
    n = v / 2
  else
    n = v * 0.5 + 1
  end
  local t = 0
  for i = 1, 3 do t = t + n end
  return floor(t)
end

local function run(n)
  local total = 0
  for i = -n, n do
    local hi, lo = split(i * 37)
    total = total + hi * 7 + lo + thirds(i * 5) + rewritten(i) + shared(i) + branchy(i)
  end
  return total
end

print(run(4))
print(run(500))
-- EXPECT: 1003
-- EXPECT: 125001
