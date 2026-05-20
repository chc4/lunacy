-- EXPECT: 1	2	3
local function multi() return 1,2,3,4 end local function fast() local a, b, c = multi() print(a,b,c) end fast()