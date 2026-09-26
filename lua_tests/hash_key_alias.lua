-- A table's hash key used through another register holding it, which a MOVE
-- gives the table's shape: at a higher slot than the one the key was made for,
-- and after the first register is overwritten (its key moving to the other,
-- `set_types`' migration). Reads and writes through it use the key's witness,
-- and a write through it is the table's.
local function f(t)
  local x = t
  local s = x.a
  local y = x
  s = s + y.a              -- through a second register, at a higher slot
  x = nil                  -- `x`'s register overwritten: its key moves to `y`
  s = s + y.a
  y.a = y.a + 1
  return s + y.a + t.a
end
print(f({a = 1}))
print(f({a = 5}))
f.__jit = 1
print(f({a = 1}))
print(f({a = 5}))
-- EXPECT: 7
-- EXPECT: 27
-- EXPECT: 7
-- EXPECT: 27
