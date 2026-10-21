-- A loop whose variable it sets each iteration, as a constant or an integer's
-- quotient by one, from a value from before it: from another constant, or a
-- value nothing is known of. Where the value from before the loop and the one
-- from its back edge meet, the loop is one version, whichever first.
-- `jit.versions()` tells how many versions the code it is in has; the most it
-- told in loops run often enough for JIT code is printed. Each function calls
-- it once before its loop, so the loop is entered knowing the `versions`
-- upvalue's identity, as its back edge does: no version of the loop is told
-- apart by learning it.
-- Its output counts versions, which an injected effect may rightly add to.
-- FEATURE: !conservative_information

local versions = jit.versions

-- From another constant.
local function constants(n)
  local a, seen = 0, versions()
  for i = 1, n do
    seen = versions()
    a = 1
  end
  return a, seen
end

-- From a value nothing is known of: the back edge comes with the constant.
local function constant(n, start)
  local a, seen = start * 3, versions()
  for i = 1, n do
    seen = versions()
    a = 1
  end
  return a, seen
end

-- From a double: the back edge comes with the quotient.
local function quotient(n, start)
  local q, seen = start * 0.5, versions()
  for i = 1, n do
    seen = versions()
    q = i / 2
  end
  return q, seen
end

local function run(n)
  local total, most = 0, 0
  for i = 1, n do
    local a, s1 = constants(i)
    local b, s2 = constant(i, i)
    local c, s3 = quotient(i, i)
    total = total + a + b + c
    most = math.max(most, s1, s2, s3)
  end
  return total, most
end

print((run(4)))
print(run(500))
-- EXPECT: 13
-- EXPECT: 63625	1
