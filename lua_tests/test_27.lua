-- EXPECT: 1	2	4	1
local function multi() return 1,2,3,4 end local function fast() local a, b, _, d = multi() local x = 1 print(a, b, d, x) end fast()