-- A field known to hold a string is overwritten with a value of unknown type
-- (a call's result), really a number: `UpdateHashRef` doesn't record an
-- unknown type for the hash key, so a later read of the field must not be
-- taken to be a string.
local function id(v) return v end
local function f(t, v)
  t.a = "s"
  local n = #t.a
  t.a = id(v)
  return t.a + n
end
print(f({}, 5))
print(f({}, 6))
f.__jit = 1
print(f({}, 5))
print(f({}, 6))
-- EXPECT: 6
-- EXPECT: 7
-- EXPECT: 6
-- EXPECT: 7
