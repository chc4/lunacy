-- A local one closure captured stays its cell while open: a callee setting it through the
-- closure, both inlined, sets the local, its type too.
local function run(n)
  local s = 0
  for i = 1, n do
    local x = 1
    local set = function(v) x = v end
    local function through(g, v) g(v) end
    through(set, i + 0.5)
    s = s + x
  end
  return s
end

print(run(10))
print(run(300))
run.__jit = 1
print(run(300))
-- EXPECT: 60
-- EXPECT: 45300
-- EXPECT: 45300
