-- string.gmatch and string.gsub with a function replacement, written in Lua
-- (src/library.lua): gmatch over captures, positions, empty matches and a
-- literal leading `^`; gsub's replacement kept when it returns nil or false,
-- numbers, counts and anchors. See Note [Library natives].
local words = {}
for w in string.gmatch("one two  three", "%a+") do words[#words + 1] = w end
print(table.concat(words, ","))
for k, v in string.gmatch("a=1, b=22, c=333", "(%w+)=(%w+)") do print(k, v) end
local function collect(s, p)
  local all = {}
  for m in string.gmatch(s, p) do all[#all + 1] = "[" .. m .. "]" end
  return table.concat(all)
end
print(collect("abc", "()"), collect("a,,b", "[^,]*"), collect("^a^b", "^%a"), collect(12345, "%d%d"))
print(string.gsub("hello world", "%w+", function(w) return "<" .. w .. ">" end))
print(string.gsub("$a + $b = $c", "%$(%w)", function(name)
  local values = {a = 1, b = 2}
  return values[name]
end))
print(string.gsub("abc", "%w", function(c) return string.byte(c) end))
print(string.gsub("x1y2z3", "(%a)(%d)", function(a, d) return d .. a end, 2))
print(string.gsub("aaa", "^a", function(a) return "b" end))
print(string.gsub("abc", "", function() return "-" end))
print(string.gsub("keep", "e", function() return false end))
-- EXPECT: one,two,three
-- EXPECT: a	1
-- EXPECT: b	22
-- EXPECT: c	333
-- EXPECT: [1][2][3][4]	[a][][][b][]	[^a][^b]	[12][34]
-- EXPECT: <hello> <world>	2
-- EXPECT: 1 + 2 = $c	3
-- EXPECT: 979899	3
-- EXPECT: 1x2yz3	2
-- EXPECT: baa	1
-- EXPECT: -a-b-c-	4
-- EXPECT: keep	2
