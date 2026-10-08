-- Facts about upvalues of the closures a function calls, named as paths
-- through them (Note [Upvalue paths]): inlined calls of a helper loaded from
-- an upvalue, the helper calling a native from its own upvalue; the caller
-- setting the cell the helper's upvalue shares, an inlined callee setting it
-- between two calls of the helper, and the caller swapping the helper for
-- another.
local bit = require("bit")
local op = bit.band

local function helper(a, b) return op(a, b) + 1 end
local function other(a, b) return op(b, a) * 2 end

local function calls(n)
  local acc = 0
  for i = 1, n do
    acc = acc + helper(i, 3) + helper(i, 5) + helper(i, 6)
  end
  return acc
end

local function sets(n)
  local acc = 0
  for i = 1, n do
    acc = acc + helper(i, 3)
    if i == 4 then op = bit.bor end
    acc = acc + helper(i, 5)
  end
  op = bit.band
  return acc
end

local function flip(a, b) op = bit.bxor; return a + b end
local function helper_sets(n)
  local acc = 0
  for i = 1, n do
    acc = acc + helper(i, 3)
    if i == 6 then acc = acc + flip(i, 1) end
    acc = acc + helper(i, 5)
  end
  op = bit.band
  return acc
end

local function swaps(n)
  local acc = 0
  for i = 1, n do
    acc = acc + helper(i, 3) + helper(i, 5)
    if i == 3 then helper, other = other, helper end
  end
  helper, other = other, helper
  return acc
end

local function run()
  print(calls(10), sets(10), helper_sets(10), swaps(10))
end

run()
calls.__jit = 1
sets.__jit = 1
helper_sets.__jit = 1
swaps.__jit = 1
run()
run()
-- EXPECT: 92	147	126	70
-- EXPECT: 92	147	126	70
-- EXPECT: 92	147	126	70
