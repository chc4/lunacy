-- `rawget` and `rawset`, which skip a metatable, and reading files with `io.open` and
-- `io.lines`: lua_tests/raw_and_io.txt, from the directory the tests run in.
local base = {k = 1}
local t = setmetatable({own = 2}, {__index = base})
print(t.k, rawget(t, "k"), rawget(t, "own"), rawget(t, "o" .. "wn"))
print(rawset(t, "k", 3) == t, t.k, rawget(t, "k"), base.k)
local ok, err = pcall(rawget, 5, "k")
print(ok, string.find(err, "table expected, got number", 1, true) ~= nil)

local path = "lua_tests/raw_and_io.txt"
local f = io.open(path, "rb")
print(f ~= nil, f:read("*l"))
print(f:read(3), f:read("*l"))
local rest = f:read("*a")
print(#rest > 0, f:read("*a") == "", f:read("*l"))
print(f:close())
print(pcall(f.read, f, "*l"))

local n, longest = 0, 0
for line in io.lines(path) do
  n = n + 1
  if #line > longest then longest = #line end
end
local m = 0
local g = io.open(path)
for _ in g:lines() do m = m + 1 end
g:close()
print(n, m, longest)

local missing, why = io.open("lua_tests/no such file")
print(missing, why)
-- The harness sees what `print` prints, not stdout: a write of nothing, and its result.
print(io.stdout:write(""))
-- EXPECT: 1	nil	2	2
-- EXPECT: true	3	3	1
-- EXPECT: false	true
-- EXPECT: true	first line
-- EXPECT: sec	ond line, a longer one
-- EXPECT: true	true	nil
-- EXPECT: true
-- EXPECT: false	attempt to use a closed file
-- EXPECT: 5	5	25
-- EXPECT: nil	lua_tests/no such file: No such file or directory
-- EXPECT: true
