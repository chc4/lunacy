-- EXPECT: 1	2	3	4
local function multi() return 1,2,3,4 end local function fast() print(multi()) end fast()