-- Closures made in a function LBBV runs: two sharing a captured local, one
-- writing a local its creator keeps using across the call (typed an integer
-- there, as a loop counter), one outliving its frame, and a nested one capturing
-- through its parent's upvalue. A frame's open upvalues stay open while a call
-- it makes returns.
local function counter()
  local n = 0
  local function inc() n = n + 1 end
  local function get() return n end
  return inc, get
end

local function run()
  local inc, get = counter()
  for _ = 1, 5 do inc() end
  print(get())

  local total = 0
  local function add(k) total = total + k end
  for i = 1, 10 do
    add(i)
    total = total + 1
  end
  print(total)

  local x = 1
  local function bump() x = x + 0.5 end
  local function id(v) return v end
  id(0)
  bump()
  print(x)
  x = x + 1
  print(x)

  local function outer()
    local y = 10
    local function mid()
      local function inner() y = y + 1; return y end
      return inner
    end
    local f = mid()
    f()
    return f, function() return y end
  end
  local f, g = outer()
  f()
  print(g())
end

run()
run.__jit = 1
run()
-- EXPECT: 5
-- EXPECT: 65
-- EXPECT: 1.5
-- EXPECT: 2.5
-- EXPECT: 12
-- EXPECT: 5
-- EXPECT: 65
-- EXPECT: 1.5
-- EXPECT: 2.5
-- EXPECT: 12
