-- EXPECT: 1	2	3	4
local function multi() return 1,2,3,4 end local function fast() local a, b, c, d = multi() print(a,b,c,d) end fast()