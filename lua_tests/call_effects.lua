-- A call's continuation keeps what its callee's effects don't falsify: a
-- field's type, an array's kind, a captured local's type. Each callee stores
-- what falsifies it only late in the loop, after the caller's continuation was
-- compiled for the callee without that store, which must not be trusted after.

local t = { x = 1 }
local function set_field(i, late)
  if late then t.x = i + 0.5 end
  return i
end

local arr = { 1, 2, 3 }
local function store_double(i, late)
  if late then arr[2] = 0.25 end
  return i
end

local function pure(i)
  return i + 1
end

-- The tables held in locals across the calls, with what is known of them.
local function run(n, at)
  local tt, aa = t, arr
  local s = 0
  for i = 1, n do
    local late = i > at
    s = s + tt.x
    s = s + set_field(i, late)
    s = s + tt.x
    s = s + aa[2]
    s = s + store_double(i, late)
    s = s + aa[2]
    s = s + pure(i) + aa[1] + tt.x
  end
  return s
end

-- A local its callee sets through an upvalue, from a number to a string.
local function run_captured(n, at)
  local c = 0
  local function set_c(i, late)
    if late then c = "s" .. i end
    return i
  end
  local strings, total = 0, 0
  for i = 1, n do
    c = i
    total = total + set_c(i, i > at)
    if type(c) == "string" then strings = strings + 1 else total = total + c end
  end
  return strings, total, c
end

print(run(400, 300), t.x, arr[2])
print(run_captured(400, 300))

-- Again, the callees' late stores compiled already.
t.x, arr[2] = 1, 2
print(run(400, 350), t.x, arr[2])
print(run_captured(400, 350))

-- EXPECT: 348452.25	400.5	0.25
-- EXPECT: 100	125350	s400
-- EXPECT: 299877.25	400.5	0.25
-- EXPECT: 50	141625	s400
