-- FEATURE: watchpoints
-- `jit.frozen(t)` watches a table, and `jit.tripped(t)`, a watch site, is
-- compiled knowing the table is still watched, `false` with no test, until a
-- store into it trips its watchpoint, which unpublishes the site: from then on
-- it is the native's answer. Each loop runs often enough for JIT code, checks
-- the site every iteration, and stores into the table once, at iteration `k`,
-- in a different way each; it counts the iterations finding it tripped, which a
-- stale site would leave short. And a table watched again after a trip, which
-- the site, unpublished, finds by asking.

local n, k = 400, 150

local function count(t, store)
  jit.frozen(t)
  local seen = 0
  for i = 1, n do
    if jit.tripped(t) then seen = seen + 1 end
    if i == k then store(t, i) end
  end
  return seen
end

local function element(t, i) t[1] = i end
local function field(t, i) t.x = i end
-- Vararg, so never inlined.
local function far(t, ...) t[2] = ... end
local function near(t, i) far(t, i) end
local function insert(t, i) table.insert(t, i) end
local function remove(t, i) table.remove(t) end
local function meta(t, i) setmetatable(t, {}) end

print(count({ 1, 2, 3 }, element), count({ x = 0 }, field), count({ 1, 2 }, far), count({ 1, 2 }, near))
print(count({ 1, 2 }, insert), count({ 1, 2 }, remove), count({}, meta))

-- Checked after the call that stores, as well as before it: the check after it
-- knows the table is watched from the one before, so a frame paused at the call
-- has to go on in code that doesn't, or it counts one iteration short of the
-- check before's, which a stale site would leave short too.
local function across(t, store)
  jit.frozen(t)
  local seen = 0
  for i = 1, n do
    if jit.tripped(t) then seen = seen - 1 end
    if i == k then store(t, i) end
    if jit.tripped(t) then seen = seen + 2 end
  end
  return seen
end
print(across({ 1, 2, 3 }, element), across({ 1, 2 }, far), across({ 1, 2 }, near), across({ 1, 2 }, insert))

-- The same loop, inlined into its caller, storing where the caller does.
local function inlined(t)
  jit.frozen(t)
  local seen = 0
  for i = 1, n do
    if jit.tripped(t) then seen = seen + 1 end
    if i == k then t[3] = i end
  end
  return seen
end
print(inlined({ 1, 2, 3 }))

-- A global store into a watched environment.
jit.frozen(_G)
local seen = 0
for i = 1, n do
  if jit.tripped(_G) then seen = seen + 1 end
  if i == k then watched_global = i end
end
print(seen)

-- Watched again after its trip: the site asks, from then on.
local t, again = { 1 }, 0
jit.frozen(t)
for i = 1, n do
  if jit.tripped(t) then again = again + 1 end
  if i == k then t[1] = i end
  if i == k + 50 then jit.frozen(t) end
end
print(again)
-- EXPECT: 250	250	250	250
-- EXPECT: 250	250	250
-- EXPECT: 252	252	252	252
-- EXPECT: 250
-- EXPECT: 250
-- EXPECT: 50
