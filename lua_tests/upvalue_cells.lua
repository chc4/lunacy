-- Upvalues read many times, which JIT code keeps in cells: a table read twice
-- by an inlined function; a counter shared by two closures, one of them, inlined,
-- setting it between the other's reads; an upvalue still open, a local of the
-- running function read by a closure inlined into it while it changes; and a
-- function reached through another's upvalue, whose own upvalues its inlined
-- call reads. What's read decides what's summed. Once, and in loops run often
-- enough for JIT code.

local function make()
  local data = { 3, 5, 7, 11 }
  local count = 0
  local function get(i) return data[i] + data[(i % 4) + 1] end
  local function bump(n) count = count + n end
  local function read() return count end
  local function swap() data = { 1, 2, 3, 4 } end
  return get, bump, read, swap
end

local helper
do
  local scale = 10
  local function scaled(v) return v * scale end
  helper = function(v) return scaled(v) + scale end
end

local function run(n)
  local get, bump, read, swap = make()
  local total = 0
  for k = 1, n do
    total = total + get(k % 4 + 1) + read()
    bump(k % 3)
    total = total + read() + get(1)
    if k == n - 3 then swap() end
    local open = k
    local function peek() return open * 2 end
    total = total + peek()
    open = open + 1
    total = total + peek() + helper(k % 5)
  end
  return total
end

print(run(3))
print(run(500))
-- EXPECT: 199
-- EXPECT: 777793
