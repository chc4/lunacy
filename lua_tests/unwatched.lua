-- A store's check finds a table unwatched, and the stores after it check it no
-- more, until a watch may have made it watched: here a freeze, by a callee or
-- directly, between a store that found the table unwatched and one through the
-- same name, which must trip so the frozen element read in between is read
-- again. And stores into tables nothing watches, twice an iteration.

local frozen = jit and jit.frozen or function(t) return t end

local function freeze(t) return frozen(t) end

local function through_callee(t, n)
  local total = 0
  for i = 1, n do
    t[3] = i
    local f = freeze(t)
    total = total + f[1]
    t[1] = t[1] + 1
  end
  return total
end

local function direct(t, n)
  local total = 0
  for i = 1, n do
    t[3] = i
    local f = frozen(t)
    total = total + f[1]
    t[1] = t[1] + 2
  end
  return total
end

local function swaps(t, n)
  for i = 1, n do
    t[1], t[2] = t[2], t[1] + 1
  end
  return t[1] + t[2]
end

print(through_callee({ 0, 0, 0 }, 2000))
print(direct({ 0, 0, 0 }, 2000))
print(swaps({ 0, 0 }, 3001))
-- EXPECT: 1999000
-- EXPECT: 3998000
-- EXPECT: 3001
