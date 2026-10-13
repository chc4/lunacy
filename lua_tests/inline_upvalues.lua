-- An inlined callee's upvalue a slot holds is that slot's: calling it, once a peeled call has
-- taught its caller the upvalue's value, makes no frame. One making its frame after reading an
-- upvalue, as a store into an upvalue does, reads it again from where the frame keeps it.

local abs, k, last = math.abs, 7, 0

local function leaf(x)
  return abs(x - k) + k
end

local function framed(x)
  local y = x + k
  last = y
  return y + k
end

local s = 0
for i = 1, 1000 do
  s = s + leaf(i) + framed(i)
end
print(s, last)
-- EXPECT: 1015042	1007
