-- A native whose only result is an argument (setmetatable's table) gives its type to the call's
-- result, and to the continuations of calls it returns to in tail position.
local V = {}
V.__index = V
function V.new(x, y)
  return setmetatable({x = x, y = y}, V)
end
function V:minus(o)
  return V.new(self.x - o.x, self.y - o.y)
end
function V:len2()
  return self.x * self.x + self.y * self.y
end

local function run(n)
  local s = 0
  local step = V.new(1, 2)
  local v = V.new(n, n)
  for i = 1, n do
    v = v:minus(step)
    local w = setmetatable({x = i, y = -i}, V)
    s = s + v:len2() + w:len2()
  end
  return s, v.x, v.y
end

print(run(10))
print(run(300))
run.__jit = 1
print(run(300))
-- EXPECT: 1395	0	-10
-- EXPECT: 36045350	0	-300
-- EXPECT: 36045350	0	-300
