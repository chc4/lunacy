-- Array stores of constant values (true, false, a number, a string) at a
-- constant index and at an index in a register, in the array part; beside them,
-- appends and stores at a double's key, which go elsewhere. Once, and in a loop
-- run often enough for JIT code.

local function run(n)
  local t = {}
  for i = 1, n do t[i] = 0 end
  for i = 1, n do t[i] = true end
  for i = 2, n, 2 do t[i] = false end
  t[1] = 7
  t[3] = "three"
  t[n + 1] = true
  t[1.5] = "half"
  local trues, falses = 0, 0
  for i = 1, n + 1 do
    if t[i] == true then trues = trues + 1 elseif t[i] == false then falses = falses + 1 end
  end
  return t[1] .. " " .. t[3] .. " " .. trues .. " " .. falses .. " " .. #t .. " " .. t[1.5]
end

local first = run(10)
local same = true
for i = 1, 300 do
  if run(10) ~= first then same = false end
end
print(first)
print(run(4))
print(same)
-- EXPECT: 7 three 4 5 11 half
-- EXPECT: 7 three 1 2 5 half
-- EXPECT: true
