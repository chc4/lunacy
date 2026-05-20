-- EXPECT: 1
-- EXPECT: 202
local function fast() local t = {} t.a = 1 t.b = 2 print(t.a) for i = 1, 100 do t.c = t.a + t.b t.b = t.a + t.c end print(t.b) end fast()