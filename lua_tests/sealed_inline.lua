-- An inlined call, sealed by a run of it reaching a return, runs a path its first runs never took
-- as a call of the callee's own code, once that path's code is past its budget: from a frame made,
-- from one only entered, and from a call inlined in another. Fields turning one by one to floats
-- where they held integers, of types the caller doesn't know, make guards fail on new paths.
local blackbox = blackbox or function(...) return ... end
local count = 0
local cell = { v = 0, a = 0, b = 0, c = 0, d = 0, e = 0, f = 0, g = 0 }

local function made(t)
  count = count + 1
  local z = t.v * 2
  return z + 1
end

-- Returning fewer results than the call takes, through a thunk.
local function entered(t, y)
  local z = t.v * 2 + t.a * 3 + t.b * 4 + t.c * 5 + t.d * 6 + t.e * 7 + t.f * 8 + t.g * 9
  return z + y
end

local function outer(t)
  local r, none = entered(t, 1)
  return r + (none or 0)
end

local function run(n)
  local s = 0
  for i = 1, n do
    local phase = math.floor(i * 9 / n)
    cell.v = blackbox(phase >= 1 and i + 0.5 or i)
    cell.a = blackbox(phase >= 2 and i + 0.5 or i)
    cell.b = blackbox(phase >= 3 and i + 0.5 or i)
    cell.c = blackbox(phase >= 4 and i + 0.5 or i)
    cell.d = blackbox(phase >= 5 and i + 0.5 or i)
    cell.e = blackbox(phase >= 6 and i + 0.5 or i)
    cell.f = blackbox(phase >= 7 and i + 0.5 or i)
    cell.g = blackbox(phase >= 8 and i + 0.5 or i)
    local r, none = entered(cell, i)
    s = s + made(cell) + r + outer(cell) + (none or 0)
  end
  return s
end

print(run(50))
run.__jit = 1
print(run(300))
print(count)
-- EXPECT: 117060
-- EXPECT: 4114745
-- EXPECT: 350
