-- The library natives: base functions, string, table (with LuaJIT's table.new
-- and table.clear), io.write, LuaJIT's bit, and require of built-in modules.
-- Expected output is LuaJIT's.
print(type(nil), type(true), type(1), type("s"), type({}), type(print))
print(tostring(12), tostring(true), tostring(nil), tostring("x"))
print(tonumber("42"), tonumber(" 1.5 "), tonumber("0x10"), tonumber("zz"), tonumber("ff", 16), tonumber(7))

local s = "hello world"
print(string.len(s), string.sub(s, 1, 5), string.sub(s, -5), string.sub(s, 7), #string.sub(s, 3, 2))
print(string.byte(s), string.byte(s, 5), string.byte(s, -1))
local b1, b2, b3 = string.byte("abc", 1, 3)
print(b1, b2, b3)
print(string.char(72, 105, 33))

require("table.new")
require("table.clear")
local t = table.new(8, 0)
print(#t)
table.insert(t, "a")
table.insert(t, "c")
table.insert(t, 2, "b")
print(#t, table.concat(t), table.concat(t, ", "), table.concat(t, "-", 2, 3))
table.clear(t)
print(#t)
table.insert(t, 1)
table.insert(t, 2.5)
print(table.concat(t, " "))

-- (io.write goes to stdout, which the golden tests don't capture.)
io.write_devnull("discarded")

local bit = require("bit")
print(bit.band(0xff, 0x0f, 0x3c), bit.bor(1, 2, 4), bit.bxor(0xff, 0x0f), bit.bnot(0))
print(bit.lshift(1, 4), bit.lshift(1, 31), bit.rshift(-1, 28), bit.arshift(-256, 4))
print(bit.rol(1, 31), bit.ror(1, 1), bit.bswap(0x12345678), bit.tobit(2^32 + 5))

local function f(x) return bit.band(x, 7) + string.len(tostring(x)) end
print(f(13), f(100))
f.__jit = 1
print(f(13), f(100))
-- EXPECT: nil	boolean	number	string	table	function
-- EXPECT: 12	true	nil	x
-- EXPECT: 42	1.5	16	nil	255	7
-- EXPECT: 11	hello	world	world	0
-- EXPECT: 104	111	100
-- EXPECT: 97	98	99
-- EXPECT: Hi!
-- EXPECT: 0
-- EXPECT: 3	abc	a, b, c	b-c
-- EXPECT: 0
-- EXPECT: 1 2.5
-- EXPECT: 12	7	240	-1
-- EXPECT: 16	-2147483648	15	-16
-- EXPECT: -2147483648	-2147483648	2018915346	5
-- EXPECT: 7	7
-- EXPECT: 7	7
