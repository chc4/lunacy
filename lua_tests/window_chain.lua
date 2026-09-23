-- Chained arithmetic inside a function, so the specializer compiles it into runs
-- of register-window ops: results feed later ops, inputs stay live after being
-- read, a result overwrites its own input, and an operand is read twice.
local function chain(a, b)
  local x = a + b
  local y = x * a
  local z = x - y
  a = a + z
  local w = a * a
  return a, b, x, y, z, w
end
for i = 1, 3 do
  print(chain(i, 2 * i))
end
-- EXPECT: 1	2	3	3	0	1
-- EXPECT: -4	4	6	12	-6	16
-- EXPECT: -15	6	9	27	-18	225
