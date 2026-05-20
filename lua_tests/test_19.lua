-- EXPECT: test post
-- EXPECT: 2
local function fast() local t = {} t.a = "test" print(t.a .. " post") t.a = 1 print(t.a + 1) end fast()