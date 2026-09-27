-- Ways into one arithmetic instruction that read different operand types can
-- meet in one subblock (Note [Subblocks]); what the instruction then does must
-- not depend on the way that compiled it. Each function is run with operands
-- in several orders, so each way compiles the shared subblock first in one of
-- them.

-- x + K with x unknown takes the number path, finding x's type by a failed
-- table guard; with x an integer, it takes the integer path, whose overflow
-- guard failing continues where the unknown way found an integer.
local function add_k(x)
  return x + 2147483000
end

local function add_k_known(n, start)
  local sum = 0
  local x = start
  for i = 1, n do
    sum = sum + add_k(x)
    x = x + 1
  end
  return sum
end

-- Registers: one read as a number of unknown encoding and found a double,
-- meeting one known to be a double, and integers that overflow.
local function add_rr(a, b)
  return a + b
end

local function mix(values, n)
  local total = 0
  for i = 1, n do
    local a = values[(i % #values) + 1]
    local b = values[((i * 3) % #values) + 1]
    total = total + add_rr(a, b) + add_rr(b, a)
  end
  return total
end

-- The same through a loop-carried register whose type changes between
-- iterations, so the loop header joins them to a number.
local function carried(n)
  local x = 1
  local total = 0
  for i = 1, n do
    total = total + (x + 2147483600)
    if i % 3 == 0 then x = x + 0.5 elseif i % 3 == 1 then x = 2147483000 + i else x = i end
  end
  return total
end

-- One ADD with two predecessors, whose contexts differ only in x: an integer
-- (set on the flagged path) or unknown (the parameter). The known way's
-- overflow guard fails; the unknown way skips the integer path, a step
-- decided as failed at the same point, then finds x an integer by the number
-- path's failed table guard, which the known way decides statically. Both
-- continue through the same steps. `add_branch_a` compiles from the unknown
-- way first, `add_branch_b` from the known one.
local function add_branch_a(x, flag)
  if flag then x = 2147483000 end
  return x + 2147483000
end
local function add_branch_b(x, flag)
  if flag then x = 2147483000 end
  return x + 2147483000
end
print(add_branch_a(1, false), add_branch_a(0, true), add_branch_a(2, false), add_branch_a(0.5, false))
print(add_branch_b(0, true), add_branch_b(1, false), add_branch_b(0, true), add_branch_b(0.5, false))

-- Each order of first uses.
print(add_k(1), add_k(1000), add_k(0.5))
print(add_k_known(20, 640), add_k_known(20, 0))
print(add_k(700), add_k(-5), add_k(2.25))

local ints = { 1, 2147483000, -7, 2147483647, 5 }
local doubles = { 0.5, 1e10 + 0.5, -3.25, 2.5 }
local both = { 3, 0.75, 2147483600, -1.5, 9 }
print(mix(ints, 40), mix(doubles, 40), mix(both, 40))
print(mix(both, 41), mix(ints, 41), mix(doubles, 41))

print(carried(60), carried(61))

-- Compares read their operands' types the same way.
local function lt(a, b)
  if a < b then return 1 end
  return 0
end
local function compares(values, n)
  local count = 0
  for i = 1, n do
    count = count + lt(values[(i % #values) + 1], values[((i * 7) % #values) + 1])
  end
  return count
end
print(compares(ints, 50), compares(doubles, 50), compares(both, 50))
-- EXPECT: 2147483001	4294966000	2147483002	2147483000.5
-- EXPECT: 4294966000	2147483001	4294966000	2147483000.5
-- EXPECT: 2147483001	2147484000	2147483000.5
-- EXPECT: 42949672990	42949660190
-- EXPECT: 2147483700	2147482995	2147483002.25
-- EXPECT: 137438932672	400000000010	68719475560
-- EXPECT: 68719475558.5	146028865966	420000000016
-- EXPECT: 171798677761.5	173946161421
-- EXPECT: 20	12	20
