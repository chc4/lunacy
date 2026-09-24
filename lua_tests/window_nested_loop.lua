-- A nested loop whose inner loop runs a few times per outer iteration, so
-- every edge of both loops has run before the inner loop turns hot: the
-- region compiled from its hot block holds both loops, entered inside the
-- inner one. The branch makes the inner loop span several blocks.
local function f(n, m, a)
  local s = 0
  for i = 1, n do
    local t = i * a
    for j = 1, m do
      if j > 5 then
        s = s + t * j - i
      else
        s = s - j
      end
    end
    s = s - t
  end
  return s
end
print(f(200, 10, 3))
print(f(200, 10, 3))
print(f(50, 4, 7))
-- EXPECT: 2248200
-- EXPECT: 2248200
-- EXPECT: -9425
