-- Every closure sharing a local's open cell is known, but a place holding one the context doesn't
-- know holds it learns its upvalue too: a store to the local is one to that place's upvalue.
-- Not inlined: its result is a closure the caller doesn't know is its argument.
local function id(...) return (...) end

local function run(n)
  local s = 0
  for i = 1, n do
    local x = i
    local c = function() return x end
    local d = id(c)
    local before = d()
    x = i * 7
    s = s + before + d()
  end
  return s
end

print(run(10))
print(run(300))
run.__jit = 1
print(run(300))
-- EXPECT: 440
-- EXPECT: 361200
-- EXPECT: 361200
