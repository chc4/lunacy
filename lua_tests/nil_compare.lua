-- Comparisons with nil, decided statically once the operand's type is known:
-- `==` and `~=` in either order, against nil and against a number.
local function kernel(t, n, offset)
  local sum = 0
  for i = 1, n do
    local k = i + offset
    local v = t[k]
    if v == nil then v = 0 end
    t[k] = v + i
    sum = sum + v
  end
  return sum
end
local function describe(v)
  local s = ""
  if v == nil then s = s .. "eq;" end
  if v ~= nil then s = s .. "ne;" end
  if nil == v then s = s .. "req;" end
  if nil ~= v then s = s .. "rne;" end
  return s
end
local t = {}
for i = 1, 8 do t[i] = i end
print(kernel(t, 8, 0), kernel(t, 8, -16), kernel(t, 8, -16))
print(describe(nil), describe(3))
kernel.__jit = 1; describe.__jit = 1
local u = {}
for i = 1, 8 do u[i] = i end
print(kernel(u, 8, 0), kernel(u, 8, -16), kernel(u, 8, -16))
print(describe(nil), describe(3))
-- EXPECT: 36	0	36
-- EXPECT: eq;req;	ne;rne;
-- EXPECT: 36	0	36
-- EXPECT: eq;req;	ne;rne;
