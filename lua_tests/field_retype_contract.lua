-- A field an integer until its first store makes it a double, as a body built from
-- whole constants is: the code that found it an integer is contracted, and the
-- loop goes on with it a double. See Note [Field types].
local function step(bodies)
  local s = 0
  for i = 1, #bodies do
    local b = bodies[i]
    b.x = b.x + b.v
    s = s + b.x
  end
  return s
end
step.__jit = 1

local bodies = { { x = 0, v = 0.5 }, { x = 1.5, v = 0.25 } }
for _ = 1, 4 do print(step(bodies)) end
-- EXPECT: 2.25
-- EXPECT: 3
-- EXPECT: 3.75
-- EXPECT: 4.5

-- A field genuinely of both: an integer stored again after it was made a double.
local function bump(t, k) t.n = t.n + k return t.n end
bump.__jit = 1
local t = { n = 1 }
print(bump(t, 0.5), bump(t, 1), bump(t, 0.5))
t.n = 7
print(bump(t, 1), bump(t, 0.5))
-- EXPECT: 1.5	2.5	3
-- EXPECT: 8	8.5
