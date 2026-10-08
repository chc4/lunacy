-- A global read whose cache misses in JIT code, which refills it on the op's
-- cold path: a new global moves the environment's entries after the read is
-- compiled (Note [Global caches]). A string method's lookup is copied first:
-- its op's hot path is the same code as the global read's, but its cold path
-- reads the strings' table, not the environment.
local function method(s)
  return s:upper()
end
local function read(s)
  return type(string), s
end
print(method("abc"), read("abc"))
method.__jit = 1
read.__jit = 1
print(method("def"), read("def"))
fresh_global = true
print(read("ghi"))
-- EXPECT: ABC	table	abc
-- EXPECT: DEF	table	def
-- EXPECT: table	ghi
