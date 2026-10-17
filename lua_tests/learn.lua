-- `jit.learn(t)` learns what the specializer can know of t's fields once, when
-- it first runs: a hash key for each of its string keys, with its field's type,
-- and each array's kind. Code after it reads the fields as it would after
-- loading them, and still finds them changed: a field set to a value of another
-- type, an array given an element of another kind.

local learn = jit and jit.learn or function(t) return t end

local function machine()
  local m = { ints = {}, nums = {}, mixed = { 1, "a", true }, n = 3, name = "m" }
  for i = 1, 8 do m.ints[i] = i end
  for i = 1, 8 do m.nums[i] = i + 0.5 end
  m.sum = function(t) local s = 0 for i = 1, #t do s = s + t[i] end return s end
  return m
end

local function run(m, n)
  m = learn(m)
  local total = 0
  for i = 1, n do
    local ints, nums = m.ints, m.nums
    total = total + ints[i % 8 + 1] + nums[i % 8 + 1] + m.n + #m.mixed
    if i == math.floor(n / 2) then
      -- An array of another kind, and a field of another type, after learning.
      m.ints[3] = 2.25
      m.n = 0.5
    end
  end
  return total + m.sum(m.ints)
end

print(run(machine(), 10))
print(run(machine(), 2000))
learn(machine())
-- EXPECT: 169
-- EXPECT: 28441.5
