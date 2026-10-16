-- An inlined callee's upvalue open onto its caller's local has the type the local has at each
-- call, though the caller retyped the local after an earlier inlined call returned.
local function run(n)
  local k
  local function get() return k + 1 end
  local s = 0
  for i = 1, n do
    k = 1
    s = s + get()
    k = 0.5
    s = s + get()
  end
  return s
end

print(run(10))
print(run(200))
run.__jit = 1
print(run(200))
-- EXPECT: 35
-- EXPECT: 700
-- EXPECT: 700
