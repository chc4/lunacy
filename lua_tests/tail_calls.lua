-- Tail calls replace the caller's frame (Note [Tail calls]): deep tail
-- recursion, mutual recursion, vararg functions on either side, natives and
-- what isn't specialized in tail position, every result passed through,
-- upvalues closed first, and a tail caller's effects reaching the continuation
-- of the call that returns through it.

local function count_down(n, acc)
  if n == 0 then return acc end
  return count_down(n - 1, acc + 1)
end

local is_even, is_odd
function is_even(n) if n == 0 then return true end return is_odd(n - 1) end
function is_odd(n) if n == 0 then return false end return is_even(n - 1) end

local function sum(...)
  local args, s = { ... }, 0
  for i = 1, #args do s = s + args[i] end
  return s
end
local function forward(...) return sum(...) end
local function to_fixed(a, b, ...) return count_down(a, b) end

local function floor_of(x) return math.floor(x) end
local function three() return 1, 2, 3 end
local function pass_all() return three() end
local function pass_through_native(t) return unpack(t) end

-- A closure over the frame being replaced keeps its value.
local function make_counter(start)
  local n = start
  local function get() return n end
  n = n + 1
  return get, count_down(0, 0)
end

-- The tail caller stores into a table before tail-calling a function that
-- stores nothing: the caller's continuation must not trust what it knew of
-- the table's field.
local t = { x = 1 }
local function pure(v) return v + 1 end
local function store_then_tail(v, late)
  if late then t.x = v + 0.5 end
  return pure(v)
end
local function effects(n, at)
  local tt = t
  local s = 0
  for i = 1, n do
    s = s + tt.x
    s = s + store_then_tail(i, i > at)
    s = s + tt.x
  end
  return s
end

print(count_down(200000, 0))
print(is_even(100001), is_odd(100001))
print(forward(1, 2, 3, 4), to_fixed(10, 5, 'extra', 'args'))
print(floor_of(3.75), pass_all())
print(pass_through_native({ 4, 5, 6 }))
local get, zero = make_counter(41)
print(get(), zero)
print(effects(400, 300), t.x)
t.x = 1
print(effects(400, 350), t.x)
local total = 0
for i = 1, 300 do total = total + count_down(i, 0) + floor_of(i + 0.5) end
print(total)
return count_down(10, 0)

-- EXPECT: 200000
-- EXPECT: false	true
-- EXPECT: 10	15
-- EXPECT: 3	1	2	3
-- EXPECT: 4	5	6
-- EXPECT: 42	0
-- EXPECT: 151000.5	400.5
-- EXPECT: 118500.5	400.5
-- EXPECT: 90300
