-- A method found on an object's class through `__index`: the object lacks it,
-- which its lookup's first step expects; one object shadowing it with its own
-- field takes the other way. See Note [Table metatables].
local Class = {}
Class.__index = Class
function Class.new(v) return setmetatable({ v = v }, Class) end
function Class:get() return self.v end

local function call(o) return o:get() end
call.__jit = 1

local a, b = Class.new(1), Class.new(2)
print(call(a), call(b), call(a))
b.get = function(self) return self.v * 10 end
print(call(a), call(b), call(a))
b.get = nil
print(call(b))
-- EXPECT: 1	2	1
-- EXPECT: 1	20	1
-- EXPECT: 2
