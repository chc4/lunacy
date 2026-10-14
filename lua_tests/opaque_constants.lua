-- A slot holding a constant across a call the specializer doesn't see: the
-- call can't write it, so the fact survives, as a loop's step does across an
-- opaque call in its body; the slots the call does write, its function's,
-- its arguments' and its results', lose theirs. `blackbox` is the harness's
-- opaque native, returning its arguments.
local blackbox = blackbox or function(...) return ... end

local function each(t, fn)
  for i = 1, #t do
    fn(t[i])
  end
end
local function run(n)
  local t = {}
  for i = 1, n do t[i] = i end
  local sum = 0
  -- An opaque call in the loop body, inlined from `each`'s callback.
  each(t, function(v)
    sum = sum + blackbox(v)
  end)
  -- Constants in the slots an opaque call writes: its function, arguments and result.
  local one, two = 1, 2
  local r = blackbox(n, one)
  local three = one + two
  return sum, r, three
end
print(run(10))
for _ = 1, 30 do run(20) end
print(run(5))
-- EXPECT: 55	10	3
-- EXPECT: 15	5	3

-- A constant passed to an opaque call, and its slot reused for the result.
local function reuse(n)
  local k = 4
  k = blackbox(n)
  local step = -1
  local s = 0
  for i = k, 1, step do
    s = s + blackbox(i)
  end
  return k, s
end
for _ = 1, 30 do reuse(3) end
print(reuse(3))
print(reuse(7))
-- EXPECT: 3	6
-- EXPECT: 7	28
