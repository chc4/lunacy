-- The math library's one-number functions as window ops: called directly, and
-- passed as an argument and called through it, on integers and doubles, their
-- results used in arithmetic. Once, and in a loop run often enough for JIT code.

local floor, ceil, sqrt, abs, sin, cos, tan = math.floor, math.ceil, math.sqrt, math.abs, math.sin, math.cos, math.tan

local function apply(f, n)
  local s = 0
  for i = 1, n do
    s = s + f(i * 0.5 - 2)
  end
  return s
end

local function direct(n)
  local s = 0
  for i = 1, n do
    local x = i * 0.25 - 1
    s = s + floor(x) + ceil(x) + abs(x) + sqrt(i) + sin(x) + cos(x) + tan(x * 0.1) + floor(i) + abs(-i)
  end
  return s
end

local function run()
  local out = {}
  out[#out + 1] = string.format("%.6f", direct(20))
  out[#out + 1] = string.format("%.6f", apply(floor, 20))
  out[#out + 1] = string.format("%.6f", apply(ceil, 20))
  out[#out + 1] = string.format("%.6f", apply(abs, 20))
  out[#out + 1] = string.format("%.6f", apply(sin, 20))
  out[#out + 1] = string.format("%.6f", apply(cos, 20))
  out[#out + 1] = string.format("%.6f", apply(sqrt, 20) == apply(sqrt, 20) and 1 or 0)
  out[#out + 1] = floor(-2.5) .. " " .. ceil(-2.5) .. " " .. abs(-3) .. " " .. floor(7)
  local joined = table.concat(out, " ")
  return joined
end

local first = run()
local same = true
for i = 1, 300 do
  if run() ~= first then same = false end
end
print(first)
print(same)
-- EXPECT: 590.049873 60.000000 70.000000 71.000000 0.419358 3.853192 0.000000 -3 -2 3 7
-- EXPECT: true
