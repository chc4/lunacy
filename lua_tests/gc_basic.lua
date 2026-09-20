-- Build a lot of per-iteration garbage while keeping one live structure,
-- forcing collections in between, and verify the live data survived intact.
local function build(n)
  local t = {}
  for i=1,n do t[i] = { i, i*2 } end
  return t
end

local live = build(100)
for iter=1,50 do
  local garbage = build(200) -- unreachable after each iteration
  collectgarbage("step")
end
collectgarbage("collect")

local sum = 0
for i=1,100 do sum = sum + live[i][1] + live[i][2] end
print(sum)
-- EXPECT: 15150
