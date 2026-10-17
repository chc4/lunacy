-- A closure making a closure of its upvalue shares its closed cell with it: a set through the
-- first is one through the second.
local function run(n)
  local s = 0
  for i = 1, n do
    local c
    do
      local x = i
      c = function(v, make)
        if make then return function() return x end end
        if v then x = v end
        return x
      end
    end
    local g = c(nil, true)
    local before = g()
    c(i * 7)
    s = s + before + g()
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
