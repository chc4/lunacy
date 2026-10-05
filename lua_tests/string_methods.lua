-- string.lower and string.upper, and string methods: a string's fields are
-- the string library's, by `:` and by `.`, through a cached constant key or
-- any other key, with a string from a constant or made at run time, and a
-- function added to the library. Run interpreted, then with the functions
-- JIT compiled. See Note [String methods].
local function shout(words)
  local out = {}
  for i = 1, #words do
    out[#out + 1] = words[i]:upper() .. "!"
  end
  return table.concat(out, " ")
end
local function describe(s)
  return s:len(), s:lower(), s:sub(2, 3), ("x"):rep(3), s.upper(s)
end
local function lookup(s, name)
  return s[name] == string[name], s[name] ~= nil
end
local function header(line)
  local name, value = line:match("^([^:]+):%s*(.-)$")
  return name:lower(), value
end
function string.twice(s) return s .. s end
local function twice(s) return s:twice() end
local function run()
  print(string.lower("MiXeD 123"), string.upper("MiXeD 123"))
  print(shout({"hey", "you", "there"}))
  print(describe("HeLLo"))
  print(lookup("abc", "find"), lookup("abc", "nothing"))
  print(header("Content-Type: text/html"))
  print(twice("ab"))
end
run()
shout.__jit = 1
describe.__jit = 1
lookup.__jit = 1
header.__jit = 1
twice.__jit = 1
run()
-- EXPECT: mixed 123	MIXED 123
-- EXPECT: HEY! YOU! THERE!
-- EXPECT: 5	hello	eL	xxx	HELLO
-- EXPECT: true	true	false
-- EXPECT: content-type	text/html
-- EXPECT: abab
-- EXPECT: mixed 123	MIXED 123
-- EXPECT: HEY! YOU! THERE!
-- EXPECT: 5	hello	eL	xxx	HELLO
-- EXPECT: true	true	false
-- EXPECT: content-type	text/html
-- EXPECT: abab
