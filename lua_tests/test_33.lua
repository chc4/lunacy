-- EXPECT: 4
print(#("a\0" .. "b\0"))
-- EXPECT: 4
print(#("a" .. "b\0\0"))
