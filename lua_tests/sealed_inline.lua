-- An inlined call, sealed by a run of it reaching a return, runs a path its first runs never took
-- as a call of the callee's own code: from a frame made, from one only entered, and from a call
-- inlined in another. A field holding a float where it held integers, of a type the caller doesn't
-- know, makes a guard fail.
local blackbox = blackbox or function(...) return ... end
local count = 0
local cell = { v = 0 }

local function made(t)
  count = count + 1
  local z = t.v * 2
  return z + 1
end

-- Returning fewer results than the call takes, through a thunk.
local function entered(t, y)
  local z = t.v * 2
  return z + y
end

local function outer(t)
  local r, none = entered(t, 1)
  return r + (none or 0)
end

local function run(n)
  local s = 0
  for i = 1, n do
    cell.v = blackbox(i > n / 2 and i + 0.5 or i)
    local r, none = entered(cell, i)
    s = s + made(cell) + r + outer(cell) + (none or 0)
  end
  return s
end

print(run(50))
run.__jit = 1
print(run(300))
print(count)
-- EXPECT: 9100
-- EXPECT: 317100
-- EXPECT: 350
