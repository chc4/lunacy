-- jit.promote (where the Lua has none, a function returning its argument) of a
-- loop's counter: the loop is compiled again for each value, up to the number
-- of values a promote has versions for, past which it returns the counter
-- unspecialized. Run often enough for JIT code.

local promote = jit and jit.promote or function(x) return x end

local function count(n)
  local sum = 0
  for i = 1, n do sum = sum + promote(i) end
  return sum
end
print(count(600))
print(count(700))
-- EXPECT: 180300
-- EXPECT: 245350
