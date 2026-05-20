-- EXPECT: 50005000
local function foo(a) local counter = 0 for i = 1, a do counter = counter + i end return counter end print(foo(10000))