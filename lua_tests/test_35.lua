-- EXPECT: 1	2	3
-- EXPECT: 1	2
-- EXPECT: 1
-- EXPECT: 1	2	3	nil
-- multiple return values into multiple assignment (adjust up/down)
local function f() return 1, 2, 3 end
local a, b, c = f()
print(a, b, c)
local x, y = f()
print(x, y)
local p = f()
print(p)
local q, r, s, t = f()
print(q, r, s, t)
