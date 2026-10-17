-- A closure is the one sharing its closed cell, but a place holding it the context doesn't know
-- holds it learns its upvalue too: a set through the closure is one through that place.
-- Not inlined: its result is a closure the caller doesn't know is its argument.
local function id(...) return (...) end

local function run(n)
  local s = 0
  for i = 1, n do
    local c
    do
      local x = i
      c = function(v) if v then x = v end return x end
    end
    local d = id(c)
    local before = d()
    c(i * 7)
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
