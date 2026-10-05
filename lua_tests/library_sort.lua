-- table.sort, written in Lua (src/library.lua), with and without an order, of
-- numbers and of strings, which order by their bytes. See Note [Library
-- natives].
local t = {5, 2, 9, 1, 7, 3, 8, 6, 4}
table.sort(t)
print(table.concat(t, " "))
table.sort(t, function(a, b) return a > b end)
print(table.concat(t, " "))
local s, longer = "abc", "abcd"
print(s < "abd", s <= "abc", "b" < s, "abc\0" > s, s < longer, longer <= s)
local names = {"pear", "apple", "fig", "banana"}
table.sort(names)
print(table.concat(names, " "))
-- EXPECT: 1 2 3 4 5 6 7 8 9
-- EXPECT: 9 8 7 6 5 4 3 2 1
-- EXPECT: true	true	false	true	true	false
-- EXPECT: apple banana fig pear
