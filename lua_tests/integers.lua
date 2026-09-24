-- Integer keys (see Note [Integers]): discovered where a table op guards its
-- key, carried by constants, arithmetic and loop variables, and lost on
-- overflow or a fraction.
local function get(t, k) return t[k] end
local function set(t, k, v) t[k] = v end
-- A key that is an integer, then a fraction, then neither, then one again: each
-- takes the guard's fail thunk.
local function keys()
  local t = {10, 20, 30}
  set(t, 0, "zero"); set(t, -2, "minus two"); set(t, 2.5, "half"); set(t, "s", "string"); set(t, 4, 40)
  return get(t, 1), get(t, 2.5), get(t, "s"), get(t, 0), get(t, -2), get(t, 4), get(t, 5), #t
end
print(keys())
get.__jit = 1; set.__jit = 1; keys.__jit = 1
print(keys())

-- Integer arithmetic, and its overflow past the i32 range. The keys it makes
-- are ones the hash part holds, below 1 or past the array part's reach.
local function arith(n)
  local t = {}
  local lo, m = -2147483648, 65536
  for i = 1, n do t[i] = i * i end
  t[lo - 1] = "past"; t[lo + n] = "above"; t[m * m] = "product"
  local s = 0
  for i = 1, n do s = s + t[i] - t[n - i + 1] + t[i + 0] end
  return s, t[-2147483649], t[-2147483638], t[4294967296], #t
end
print(arith(10))
arith.__jit = 1
print(arith(10))

-- Loops whose variable is not an integer, or stops being one.
local function loops()
  local t = {}
  for i = 1, 3, 0.5 do t[i] = i end
  for i = -2147483646, -2147483650, -1 do t[i] = i end
  return t[1], t[1.5], t[3], t[3.5], t[-2147483647], t[-2147483650], #t
end
print(loops())
loops.__jit = 1
print(loops())
-- Array part bounds guards (see Note [Dynamic guards]) whose first key is past
-- the array part, so the in-array side is compiled second; constant keys on
-- both sides; and appends, each one past the array part.
local function at(t, k) return t[k] end
local function put(t, k, v) t[k] = v end
local function bounds()
  local t = {1, 2, 3}
  put(t, 0, "zero"); put(t, 2, "two")
  t[4] = "four"; t[3] = "three"
  local a = {}
  for i = 1, 5 do a[i] = i * 10 end
  return at(t, 9), at(t, 2), at(t, 0), t[3], t[4], t[7], t[1], #t, a[5], #a
end
print(bounds())
at.__jit = 1; put.__jit = 1; bounds.__jit = 1
print(bounds())
-- EXPECT: 10	half	string	zero	minus two	40	nil	4
-- EXPECT: 10	half	string	zero	minus two	40	nil	4
-- EXPECT: 385	past	above	product	10
-- EXPECT: 385	past	above	product	10
-- EXPECT: 1	1.5	3	nil	-2147483647	-2147483650	3
-- EXPECT: 1	1.5	3	nil	-2147483647	-2147483650	3
-- EXPECT: nil	two	zero	three	four	nil	1	4	50	5
-- EXPECT: nil	two	zero	three	four	nil	1	4	50	5
