-- An inlined call looping over another inlined call: neither frame is made by the code that runs
-- most. Code needing them makes them: a native call in the inner callee, and a call that can't be
-- inlined (a vararg function) in the outer one's loop, each first reached long after.

local function count(...)
  local a, b, c = ...
  return a + b + c
end

local function g(x, j)
  if j == 1500 then
    return x + #tostring(x)
  end
  return x + 1
end

local function f(n, j)
  local s = 0
  for i = 1, n do
    s = g(s, j)
    if j > 1800 and i == 2 then
      s = s + count(s, i, n)
    end
  end
  return s
end

local t = 0
for j = 1, 2000 do
  t = t + f(j % 7, j)
end
print(t)
-- EXPECT: 7150
