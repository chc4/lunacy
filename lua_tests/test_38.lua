-- EXPECT: 1	2	3
-- EXPECT: 0	1	2	3
-- FAILS: table constructor with a multi-return last element (SETLIST multiret)
local function f() return 1, 2, 3 end
local t = {f()}
print(t[1], t[2], t[3])
local u = {0, f()}
print(u[1], u[2], u[3], u[4])
