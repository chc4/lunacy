-- A test of a value found a function, then not one, then another function: the
-- guard of its type and the guard of its identity fail to the same thunk.
local values = {a = function() end, b = function() end}
local function truthy(name)
  local x = values[name]
  if x then return "yes" else return "no" end
end
print(truthy("a"), truthy("none"), truthy("b"), truthy("a"), truthy("none"))
-- EXPECT: yes	no	yes	yes	no
