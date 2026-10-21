-- A closure loaded back from a table's array part is known a closure, though not known to be the
-- one stored: a store to the local it captured is one to the loaded closure's upvalue.
local function run(n)
  local s = 0
  for i = 1, n do
    local x = i
    local c = function() return x end
    local d = ({c})[1]
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
