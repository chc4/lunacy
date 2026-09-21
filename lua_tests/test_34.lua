-- EXPECT: yes
-- EXPECT: yes
-- EXPECT: same
local a = {}
a["b1"] = "yes"
print(a["b1"])
print(a["b" .. "1"])
a["c" .. "2"] = "same"
print(a["c2"])
