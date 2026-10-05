-- Lua 5.1's string patterns in string.find, string.match and string.gsub:
-- plain searches, classes and sets, repetitions, anchors, captures (with
-- positions and back references), %b and %f, and gsub's string and table
-- replacements, counts and empty matches. See Note [Patterns].
print(string.find("hello world", "o w"))
print(string.find("hello world", "o", 6))
print(string.find("hello world", "l", -3))
print(string.find("a.b", ".", 1, true))
print(string.find("a+b", "+", 1, true), string.find("abc", ""), string.find("abc", "", 10))
print(string.find("  key = 42 ", "(%w+)%s*=%s*(%d+)"))
print(string.find("abc", "()b()"))
print(string.find("hello", "xyz"))
print(string.match("key: value", "^(%a+):%s*(.-)$"))
print(string.match("2024-10-05", "(%d+)-(%d+)-(%d+)"))
print(string.match("  trim me  ", "^%s*(.-)%s*$"))
print(string.match("f(a(b)c) d", "%b()"), string.match("THE (quick) fox", "%f[%a]%a+", 5))
print(string.match("say 'hi' now", "(['\"])(.-)%1"))
print(string.match("x]y", "[]]"), string.match("a-z", "[a%-z]+"), string.match("Hex FF", "%x+$"))
print(string.match("aaab", "a-b"), string.match("aaab", "a*"), string.match("b", "a?b"), string.match("", "a*"))
print(string.match("content-length: 12", "^([^:]+):%s*(%d+)"))
print(string.match(12345, "%d%d"), string.match("abc", "^b"), string.match("abc", "c$"))
print(string.gsub("hello world", "o", "0"))
print(string.gsub("hello world", "(o)", "[%1%1]", 1))
print(string.gsub("abc", "", "-"))
print(string.gsub("hello world", "%w+", "%0 %0"))
print(string.gsub("100%", "%%", " percent"))
print(string.gsub("$name is $age", "%$(%w+)", {name = "lua", age = 15}))
print(string.gsub("$name is $missing", "%$(%w+)", {name = "lua", missing = false}))
print(string.gsub("abc", "^a", "x"), string.gsub("aaa", "a", "b", 0))
print(string.gsub("one two  three", "%s+", "_"))
print(string.gsub("a,b,,c", ",", ";", 2))
print(string.gsub("x = 1, y = 2", "(%w+) = (%w+)", "%2 = %1"))
print(string.gsub("abc", "()", "%1"))
-- EXPECT: 5	7
-- EXPECT: 8	8
-- EXPECT: 10	10
-- EXPECT: 2	2
-- EXPECT: 2	1	4	3
-- EXPECT: 3	10	key	42
-- EXPECT: 2	2	2	3
-- EXPECT: nil
-- EXPECT: key	value
-- EXPECT: 2024	10	05
-- EXPECT: trim me
-- EXPECT: (a(b)c)	quick
-- EXPECT: '	hi
-- EXPECT: ]	a-z	FF
-- EXPECT: aaab	aaa	b	
-- EXPECT: content-length	12
-- EXPECT: 12	nil	c
-- EXPECT: hell0 w0rld	2
-- EXPECT: hell[oo] world	1
-- EXPECT: -a-b-c-	4
-- EXPECT: hello hello world world	2
-- EXPECT: 100 percent	1
-- EXPECT: lua is 15	2
-- EXPECT: lua is $missing	2
-- EXPECT: xbc	aaa	0
-- EXPECT: one_two_three	2
-- EXPECT: a;b;,c	2
-- EXPECT: 1 = x, 2 = y	2
-- EXPECT: 1a2b3c4	4
