-- A method call on an object in the register its method is loaded into (SELF
-- with A = B): `self` is the object, not the method. Here the object comes from
-- an upvalue, into a temporary.
local q = {}
function q:init()
  self.rows = {true, false}
end
function q:get(r)
  return self.rows[r]
end
local function run(n)
  for _ = 1, n do
    q:init()
    print(q:get(1), q:get(2))
  end
end
run(2)
run.__jit = 1
run(2)
-- EXPECT: true	false
-- EXPECT: true	false
-- EXPECT: true	false
-- EXPECT: true	false
