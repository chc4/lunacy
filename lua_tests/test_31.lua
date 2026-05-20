-- EXPECT: 1
-- EXPECT: 1
-- EXPECT: 1
-- EXPECT: 3
local function f3(a) print(#a) end local function f2(a) f3(a) end local function f1(a) f2(a) end f1('a') f1.__jit = 1 f2.__jit = 2 f3.__jit = 3 f3('a') f2('3') f1({1,2,3})