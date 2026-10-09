-- What is known of a value is known of a copy of it, a MOVE: a table copied to
-- another local and given another kind of value through the copy; the local
-- copied from given a table of another kind; a copy passed to a function
-- storing into it; and a constant copied, then the copy overwritten. What's
-- read decides what's done with it, so a copy known as what it no longer is
-- goes wrong. Once, and in loops run often enough for JIT code.

local function weigh(v)
  if type(v) == "number" then return v end
  if type(v) == "string" then return 1000 end
  return 100000
end

local function put(t, i, v) t[i] = v end

local function run(n)
  local total = 0
  for k = 1, n do
    local t = { 1, 2, 3 }
    local u = t
    total = total + weigh(u[1])
    u[2] = "s"
    total = total + weigh(t[2])
    t = { "a", "b" }
    total = total + weigh(u[3]) + weigh(t[1])
    local w = u
    put(w, 1, true)
    total = total + weigh(u[1]) + weigh(w[1])
    local c = 7
    local d = c
    d = d .. ""
    total = total + weigh(c) + weigh(d)
  end
  return total
end

print(run(1))
print(run(400))
-- EXPECT: 203011
-- EXPECT: 81204400
