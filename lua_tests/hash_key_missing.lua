-- A field read compiled for tables having the key, then run on tables
-- without it (its witness's initialization failing to the missing-key thunk),
-- and back.
local function get(t)
  return t.a
end
local function sum(n)
  local s = 0
  for i = 1, n do
    local t
    if i % 3 == 0 then t = {} else t = {a = i} end
    local v = get(t)
    if v == nil then v = 100 end
    s = s + v
  end
  return s
end
print(sum(9))
get.__jit = 1
sum.__jit = 1
print(sum(9))
-- EXPECT: 327
-- EXPECT: 327
