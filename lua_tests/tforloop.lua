-- Generic `for`: an iterator that is a Lua closure over its own state, one
-- that is a native (`string.byte`, whose result ends it by being nil), one
-- whose control variable is a string, a `break` out of one, and nested ones.
-- Once, and in a loop run often enough for JIT code.

local function range(n)
  return function(limit, i)
    if i < limit then return i + 1, i * i end
  end, n, 0
end

local function points(nx, ny)
  local y = 0
  return function(self, x)
    x = x + 1
    if x >= nx then
      x = 0
      y = y + 1
      if y >= ny then return nil, nil end
    end
    return x, y
  end, nil, -1
end

local function letters(s, prev)
  local i = #prev + 1
  if i <= #s then
    local p = string.sub(s, 1, i)
    return p
  end
end

local function run(n)
  local sum, squares = 0, 0
  for i, sq in range(n) do
    sum = sum + i
    squares = squares + sq
  end
  local cells = 0
  for x, y in points(3, 4) do
    cells = cells + x * 10 + y
  end
  local codes = 0
  for c in string.byte, "abc" do
    codes = codes + 1
    if codes > 2 then break end
  end
  local prefixes = ""
  for p in letters, "lua", "" do
    prefixes = prefixes .. p .. ","
  end
  local nested = 0
  for i in range(3) do
    for j in range(i) do
      nested = nested + i * j
    end
  end
  return sum .. " " .. squares .. " " .. cells .. " " .. codes .. " " .. prefixes .. " " .. nested
end

local first = run(10)
local same = true
for i = 1, 300 do
  if run(10) ~= first then same = false end
end
print(first)
print(run(0))
print(same)
-- EXPECT: 55 285 138 1 l,lu,lua, 25
-- EXPECT: 0 0 138 1 l,lu,lua, 25
-- EXPECT: true
