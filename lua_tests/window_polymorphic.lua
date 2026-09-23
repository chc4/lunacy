-- A guard whose failure edge is a jump: the first call forces the guard on
-- `t[i]` to a string, the second fails it, so its thunk becomes a jump to a
-- block guarding a table. The function is then compiled with the array read's
-- result and `i` live in the window across both edges of that guard.
local function len(t, i)
  local x = t[i]
  return #x + i
end
local xs = { "ab", { 1, 2, 3 } }
print(len(xs, 1))
print(len(xs, 2))
len.__jit = 1
print(len(xs, 1))
print(len(xs, 2))
-- EXPECT: 3
-- EXPECT: 5
-- EXPECT: 3
-- EXPECT: 5
