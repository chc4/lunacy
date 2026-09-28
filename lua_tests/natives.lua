-- Natives: `unpack` into a call taking every result (more values than the
-- call's slots), a table constructor and fixed results; `string.rep` and
-- `string.format`; `math.max`, `math.min` and `math.random`'s ranges; raw
-- equality of strings however they were made, and of tables. Once, and
-- in a loop run often enough for JIT code.

local function run()
  local t = {}
  for i = 1, 300 do t[i] = 65 + i % 26 end
  local s = string.char(unpack(t))
  local a, b, c = unpack({10, 20})
  local packed = {unpack({1, 2, 3, 4, 5}, 2, 4)}
  local out = {
    #s, string.sub(s, 1, 5), tostring(a) .. ',' .. tostring(b) .. ',' .. tostring(c), #packed, packed[1], packed[3],
    string.rep("ab", 3), string.rep("x", 3), string.rep("q", 0),
    string.format("%d|%5d|%-5d|%05d|%x|%X|%o", 42, 42, 42, 42, 255, 255, 8),
    string.format("%.3f|%8.2f|%e|%g|%g", 3.14159, 2.5, 12345.678, 0.0001, 1e20),
    string.format("%s|%10s|%-10s|%.2s|%c|%%|%q", "hi", "right", "left", "cut", 65, 'a "q"'),
    math.max(3, 9, 4), math.min(3, 9, 4),
    tostring(string.rep("ab", 2) == "abab"), tostring(string.rep("ab", 2) == string.rep("a", 1) .. "bab"), tostring(t == t), tostring(t == {}),
  }
  local ok = 0
  for i = 1, 200 do
    local r = math.random()
    local m = math.random(6)
    local n = math.random(-3, 3)
    if r >= 0 and r < 1 and m >= 1 and m <= 6 and m % 1 == 0 and n >= -3 and n <= 3 then ok = ok + 1 end
  end
  out[#out + 1] = ok
  return out
end

math.randomseed(42)
local first = run()
local same = 0
for i = 1, 300 do
  local again = run()
  for k = 1, #first do
    if again[k] == first[k] then same = same + 1 end
  end
end
for k = 1, #first do print(first[k]) end
print(same == 300 * #first)
-- EXPECT: 300
-- EXPECT: BCDEF
-- EXPECT: 10,20,nil
-- EXPECT: 3
-- EXPECT: 2
-- EXPECT: 4
-- EXPECT: ababab
-- EXPECT: xxx
-- EXPECT: 
-- EXPECT: 42|   42|42   |00042|ff|FF|10
-- EXPECT: 3.142|    2.50|1.234568e+04|0.0001|1e+20
-- EXPECT: hi|     right|left      |cu|A|%|"a \"q\""
-- EXPECT: 9
-- EXPECT: 3
-- EXPECT: true
-- EXPECT: true
-- EXPECT: true
-- EXPECT: false
-- EXPECT: 200
-- EXPECT: true
