-- Runs of integer arithmetic, which the peephole fuses into one operation: a
-- stack index as uxn.lua computes it, a run around a table read, one whose
-- intermediate result doesn't fit an integer though what it leaves does, and
-- one whose result doesn't fit once its inputs grow, which takes the fused
-- operation's cold path. And runs computing a key a get or a set then checks
-- is in a table's array part, which they fuse with: one whose key is sometimes
-- past it, in the hash part or nil there, which takes the cold path too. And
-- two chains of different values interleaved, held apart, one of which
-- overflows near the largest integer. And values computed and overwritten
-- before anything reads them, one overflowing, which the peephole never lays
-- out. And two chains where the second overflows after the first is written in
-- place, and a sum of a product, whose spell the product's goes on into, which
-- overflows. Once, and in loops run often enough for JIT code.

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

local function lookup(u, i)
  -- Keys 1 to 32: 1 to 8 are in the array part, 20 in the hash part.
  return u[(i - 1) % 32 + 1] or 0
end

local function store(u, i)
  u[(i + 3) % 8 + 1] = i
end

local function interleaved(i, j)
  local x = i + 3
  local y = j - 5
  x = x % 256
  y = y % 16
  return x + y
end

local function dead(i, j)
  -- Overwritten by a chain, a constant and an op the peephole can't hold.
  local t = i + 1
  t = t % 256
  t = j - 3
  local u = i * 2
  u = 7
  local v = i - 5
  v = j * -2
  return t + u + v
end

local function second(i, j)
  i = i + 1
  j = j * 2
  i = i % 1024
  return i + j
end

local function word(acc, t)
  return acc + t * 256
end

local function run(n)
  local t, u = {}, {}
  for i = 1, 16 do t[i] = i * i end
  for i = 1, 8 do u[i] = i end
  u[20] = 100
  local s1, s2, s3, s4, s5, s6, s7, s8, s9 = 0, 0, 0, 0, 0, 0, 0, 0, 0
  for i = 1, n do
    s1 = s1 + index(i)
    s2 = s2 + around(t, i)
    s3 = s3 + overwritten(2147483647 - i % 3)
    s4 = s4 + grows(i < n and i or 2147483000)
    s5 = s5 + lookup(u, i)
    store(u, i)
    s6 = s6 + interleaved(i % 7 == 0 and 2147483646 or i, i * 3)
    s7 = s7 + dead(i % 5 == 0 and 2147483647 or i, i)
    s8 = s8 + second(i, i % 11 == 0 and 1073741824 or i)
    s9 = s9 + word(i, i % 13 == 0 and 8388608 or i)
  end
  return s1, s2, s3, s4, s5, u[1] + u[8], s6, s7, s8, s9
end

print(run(10))
print(run(2000))
-- EXPECT: 55	1178	21474836470	4294966070	20	9	143	-15	175	14135
-- EXPECT: 252008	998000	4294967293999	4298960000	506436	3993	230353	-1993000	388699181454	329040047976
