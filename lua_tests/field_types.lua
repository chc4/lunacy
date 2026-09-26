-- A field read through the same code from tables where it has different types
-- (Note [Field types]): a Lua type, and a number's encoding.
local function kinds(ts)
  local out = 0
  for i = 1, #ts do
    local t = ts[i]
    out = out + #t.x
  end
  return out
end

local function encodings(ts)
  local out = 0
  for i = 1, #ts do
    local t = ts[i]
    out = out + t.x * 2 + t.y
  end
  return out
end

local function run()
  print(kinds({ { x = "abc" }, { x = { 1, 2 } }, { x = "hello" }, { x = { 1, 2, 3, 4 } } }))
  print(encodings({ { x = 1, y = 0 }, { x = 2.5, y = 0.25 }, { x = 3, y = 1 }, { x = 0.5, y = 2 } }))
end

run()
kinds.__jit = 1
encodings.__jit = 1
run()
-- EXPECT: 14
-- EXPECT: 17.25
-- EXPECT: 14
-- EXPECT: 17.25
