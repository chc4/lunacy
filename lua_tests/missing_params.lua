-- A call passing fewer arguments than the function has parameters: the rest are
-- nil, whatever their slots held before (here the caller's argument to an
-- earlier call, moved into the slot the missing parameter takes).
local bit = require("bit")
local bor = bit.bor
local function third(x, y, z) return z end

local function unknown(j)
  print(third(1, bor(j, 1)))
  print(third(1))
end
local function known(j)
  local k = j + 0
  print(third(1, bor(k, 1)))
  print(third(1, k))
end
unknown(94)
known(94)
unknown.__jit = 1
known.__jit = 1
unknown(94)
known(94)
-- EXPECT: nil
-- EXPECT: nil
-- EXPECT: nil
-- EXPECT: nil
-- EXPECT: nil
-- EXPECT: nil
-- EXPECT: nil
-- EXPECT: nil
