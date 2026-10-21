-- A closure's upvalue open onto a local stays open across a call the specializer can't see,
-- which forgets what the caller knew of the closure: an inlined call of it reads the local as it
-- is after a store into it, not the value an earlier call of it returned.
local function run(n)
  local s = 0
  for i = 1, n do
    local x = i
    local get = function() return x end
    blackbox()
    local a = get()
    x = x + 100
    local b = get()
    s = s + a * 3 + b
  end
  return s
end

print(run(10))
print(run(300))
run.__jit = 1
print(run(300))
-- EXPECT: 1220
-- EXPECT: 210600
-- EXPECT: 210600
