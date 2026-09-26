-- A table's hash keys are forgotten when its register is overwritten; one
-- before others is left orphaned, and a later hash key reuses its index (the
-- `HashKey` yield's reuse of an orphaned slot): its witness must be the new
-- key's, and a read of the first key again finds it afresh.
local function f(a, b, c)
  local s = a.p + b.q      -- hash keys for `a.p`, then `b.q`
  a = {}                   -- `a`'s register overwritten: `a.p`'s key orphaned
  s = s + c.r              -- a new hash key, in the orphaned one's index
  a.p = 5
  s = s + a.p + b.q + c.r
  return s
end
print(f({p = 1}, {q = 10}, {r = 100}))
print(f({p = 2}, {q = 20}, {r = 200}))
f.__jit = 1
print(f({p = 1}, {q = 10}, {r = 100}))
print(f({p = 2}, {q = 20}, {r = 200}))
-- EXPECT: 226
-- EXPECT: 447
-- EXPECT: 226
-- EXPECT: 447
