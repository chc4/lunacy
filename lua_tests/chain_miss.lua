-- A method two classes up: the object and its class both lack it. The middle class gaining it,
-- and losing it again, changes where it is found. See Note [Table metatables].
local Base = {}
Base.__index = Base
function Base:name() return "base " .. self.v end
local Mid = setmetatable({}, Base)
Mid.__index = Mid
local Other = setmetatable({}, Base)
Other.__index = Other

local function call(o) return o:name() end
call.__jit = 1

local a, b = setmetatable({ v = 1 }, Mid), setmetatable({ v = 2 }, Mid)
print(call(a), call(b), call(a))
function Mid:name() return "mid " .. self.v end
print(call(a), call(b))
Mid.name = nil
print(call(a), call(setmetatable({ v = 3 }, Other)), call(b))
-- EXPECT: base 1	base 2	base 1
-- EXPECT: mid 1	mid 2
-- EXPECT: base 1	base 3	base 2
