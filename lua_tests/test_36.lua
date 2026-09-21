-- EXPECT: 10	20
-- EXPECT: 10	99
-- EXPECT: 0	10	20
-- EXPECT: 10	10	20
-- EXPECT: 
-- a call's results expand as trailing call arguments (and truncate elsewhere)
local function f() return 10, 20 end
print(f())
print(f(), 99)
print(0, f())
print(f(), f())
local function none() return end
print(none())
