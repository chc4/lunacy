-- EXPECT: 1	2
-- EXPECT: 3	4
-- EXPECT: 1	2
-- EXPECT: 1	2	2
local function foo(x,y) print(x,y) return 1,2 end local function fast() local a, b, c; a, b = foo(1,2) b, c = foo(3,4) a, b = foo(1,2) print(a, b, c) end fast()