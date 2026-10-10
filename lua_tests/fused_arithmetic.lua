-- Runs of integer arithmetic, which the peephole fuses into one operation: a
-- stack index as uxn.lua computes it, a run around a table read, one whose
-- intermediate result doesn't fit an integer though what it leaves does, and
-- one whose result doesn't fit once its inputs grow, which takes the fused
-- operation's cold path. Once, and in loops run often enough for JIT code.

local function index(p)
  return (p - 1) % 256 + 1
end

local function around(t, i)
  local a = i * 3 + 7
  local b = t[a % 16 + 1]
  return (b + a) % 1000 - 1
end

local function overwritten(x)
  -- x + x doesn't fit for the largest x, but only y - x is left.
  local y = x + x
  y = y - x
  return y + 1
end

local function grows(x)
  local y = x * 2 + 1
  return y - 3
end

local function run(n)
  local t = {}
  for i = 1, 16 do t[i] = i * i end
  local s1, s2, s3, s4 = 0, 0, 0, 0
  for i = 1, n do
    s1 = s1 + index(i)
    s2 = s2 + around(t, i)
    s3 = s3 + overwritten(2147483647 - i % 3)
    s4 = s4 + grows(i < n and i or 2147483000)
  end
  return s1, s2, s3, s4
end

print(run(10))
print(run(2000))
-- EXPECT: 55	1178	21474836470	4294966070
-- EXPECT: 252008	998000	4294967293999	4298960000
