-- A loop whose arithmetic is split across two blocks by a branch in its
-- middle, so the window crosses the edge between them every iteration.
local function g(n, a, b)
  local s = 0
  for i = 1, n do
    local t = i * a + b
    if t > 10 then
      t = t - 10
    end
    s = s + t * a - b
  end
  return s
end
print(g(20, 3, 2))
g.__jit = 1
print(g(20, 3, 2))
print(g(50, 2, 5))
-- EXPECT: 1430
-- EXPECT: 1430
-- EXPECT: 4390
