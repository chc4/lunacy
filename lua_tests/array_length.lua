-- A table's length is a border (Note [Array length]): storing nil into the
-- last element shortens it, and storing nil past the end leaves it alone.
-- Each loop runs long enough to be compiled, so the stores run as window ops
-- both where the value is known to be nil and where it may be.

-- A stack: push with t[#t + 1], pop with t[#t] = nil (a nil the context knows).
local function stack(n)
  local s, most = {}, 0
  for i = 1, n do
    for j = 1, i % 7 + 1 do s[#s + 1] = j end
    if #s > most then most = #s end
    for j = 1, i % 5 + 1 do
      if #s > 0 then s[#s] = nil end
    end
  end
  return #s, most
end
print(stack(200))

-- Stores of values that are sometimes nil, into the last element.
local function maybe_nil(n)
  local t, sum = {1, 2, 3, 4}, 0
  for i = 1, n do
    local v = nil
    if i % 3 == 0 then v = i end
    t[#t] = v
    if #t == 0 then t = {1, 2, 3, 4} end
    sum = sum + #t
  end
  return sum
end
print(maybe_nil(120))

-- A hole stays a hole; clearing the end drops the nils before it too.
local function holes()
  local t = {1, 2, 3, 4, 5}
  t[2] = nil
  t[3] = nil
  local before = #t
  t[5] = nil
  t[4] = nil
  return before, #t, t[1]
end
print(holes())

-- Nil past the end stores nothing; a later key still extends from the end.
local function past_end()
  local t = {1, 2}
  t[10] = nil
  local after_nil = #t
  t[3] = 3
  return after_nil, #t
end
print(past_end())

-- table.remove and table.insert keep the end non-nil.
local function library()
  local t = {1, nil, 3}
  table.remove(t)
  local after_remove = #t
  table.insert(t, nil)
  return after_remove, #t
end
print(library())

-- A constructor ending in nil.
print(#{1, 2, nil}, #{nil, nil, 3}, #{})
-- EXPECT: 198	199
-- EXPECT: 320
-- EXPECT: 5	1	1
-- EXPECT: 2	3
-- EXPECT: 1	1
-- EXPECT: 2	3	0
