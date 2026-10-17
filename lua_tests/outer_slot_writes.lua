-- An inlined callee's upvalue open onto its caller's local holds what the local does after the
-- caller writes it, though a slot of the caller still holds the old value.
local function run(n)
  local k = 1
  local function get() return k end
  local s = 0
  for i = 1, n do
    local old = k
    s = s + get()
    k = k + 1
    s = s + get() * 1000 + old
  end
  return s
end

print(run(10))
print(run(200))
run.__jit = 1
print(run(200))
-- EXPECT: 65110
-- EXPECT: 20340200
-- EXPECT: 20340200
