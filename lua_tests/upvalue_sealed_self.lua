-- A closure passed itself sets its closed cell and then calls itself: the call reads what the set
-- stored, though the closure reached it as an argument.
local function run(n)
  local s = 0
  for i = 1, n do
    local c
    do
      local x = i
      c = function(v, self)
        local old = x
        if v then
          x = v
          return old + self()
        end
        return x
      end
    end
    s = s + c(i * 7, c)
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
