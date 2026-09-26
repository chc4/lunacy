-- Calls through an upvalue holding a native, which the specializer assumes the
-- upvalue keeps holding until it could change (Note [Fragile information]):
-- a callee setting it, the loop setting it itself, closures of one function
-- holding different natives, and the enclosing function reassigning it.
local bit = require("bit")
local op = bit.band

local function apply(n)
  local acc = 0
  for i = 1, n do acc = acc + op(i, 3) end
  return acc
end

local function switch(f) op = f end
local function mixed(n)
  local acc = 0
  for i = 1, n do
    acc = acc + op(i, 3)
    if i == 5 then switch(bit.bor) end
  end
  return acc
end

local function setter(n)
  local acc = 0
  for i = 1, n do
    acc = acc + op(i, 6)
    if i == 3 then op = bit.bxor end
  end
  return acc
end

local function make(f)
  return function(n)
    local acc = 0
    for i = 1, n do acc = acc + f(i, 5) end
    return acc
  end
end
local with_band, with_bor = make(bit.band), make(bit.bor)

local function run()
  op = bit.band
  print(apply(10))
  print(mixed(10))
  op = bit.band
  print(setter(10))
  print(apply(10))
  print(with_band(10), with_bor(10), with_band(10))
end

run()
apply.__jit = 1
mixed.__jit = 1
setter.__jit = 1
with_band.__jit = 1
with_bor.__jit = 1
run()
-- EXPECT: 15
-- EXPECT: 54
-- EXPECT: 51
-- EXPECT: 55
-- EXPECT: 21	84	21
-- EXPECT: 15
-- EXPECT: 54
-- EXPECT: 51
-- EXPECT: 55
-- EXPECT: 21	84	21
