-- `jit.frozen(t)` freezes a table: a load from it at a key the code knows is
-- its element when compiled, the value known, until a store into it trips its
-- watchpoint. A loop dispatching through frozen tables of closures, booleans
-- and integers, as an interpreter's does, finds what a store halfway through
-- put there, through a call the loop is paused in.

local frozen = jit and jit.frozen or function(t) return t end

local ops = { function(x) return x + 1 end, function(x) return x * 2 end }
local flags = { true, false }
local sizes = { 3, 5 }

local function swap(o, f)
  o[1] = function(x) return x + 7 end
  f[2] = true
end

local function run(o, f, s, n)
  o, f, s = frozen(o), frozen(f), frozen(s)
  local total = 0
  for i = 1, n do
    total = o[1](total)
    if f[1] then total = total + s[2] end
    if f[2] then total = total - s[1] end
    total = o[2](total) % 1000003
    if i == n / 2 then swap(o, f) end
  end
  return total
end

print(run(ops, flags, sizes, 10))
print(run({ ops[1], ops[2] }, { true, false }, sizes, 2000))
-- Another table through the same code: its own version.
print(run({ function(x) return x - 1 end, ops[2] }, { false, false }, { 9, 9 }, 2000))
-- EXPECT: 12462
-- EXPECT: 257084
-- EXPECT: 868637
