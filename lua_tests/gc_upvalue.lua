-- Upvalues and their captured heap objects are GC-managed and reachable only
-- through the closure. They must survive collection. (The closure is created at
-- top level and only *reads* its upvalue, to stay within the opcodes the block
-- specializer implements.)
local captured = { 10, 20, 30 }
local function get(i)
  return captured[i]
end

get(1)
-- allocate garbage + collect: `captured` (reachable only via the upvalue and the
-- top-level stack) and the closure's upvalue cell must not be reclaimed.
for i=1,100 do local junk = { i, i } end
collectgarbage("collect")
print(get(1) + get(2) + get(3))
-- EXPECT: 60
