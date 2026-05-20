-- EXPECT: 1
-- EXPECT: 2
local function maybe(a) if a > 0 then print(1) else print(2) end end maybe(1) maybe(0)