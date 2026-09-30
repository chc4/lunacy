-- Upvalues holding tables and numbers, which the specializer assumes keep the
-- type a guard found in them until something could set them (Note [Fragile
-- information]): a callee setting one late in a loop, the loop setting one
-- itself, and closures of one function holding different types.
local state = { n = 1 }
local scale = 2

local function set_state(i)
  if i == 300 then state = "done" end
  return i
end

local function set_scale(i)
  if i == 300 then scale = 0.5 end
  return i
end

local function reads(n)
  local acc = 0
  for i = 1, n do
    if type(state) == "table" then acc = acc + state.n else acc = acc + #state end
    set_state(i)
    acc = acc + scale * 2
    set_scale(i)
  end
  return acc
end

local function self_sets(n)
  local acc = 0
  for i = 1, n do
    acc = acc + scale
    if i == 200 then scale = 3.25 end
  end
  return acc
end

local function make(v)
  return function(n)
    local acc = 0
    for i = 1, n do acc = acc + v * i end
    return acc
  end
end
local ints, doubles = make(3), make(1.5)

local function run()
  state, scale = { n = 1 }, 2
  print(reads(400))
  scale = 2
  print(self_sets(400))
  print(ints(100), doubles(100), ints(100))
end

run()
reads.__jit = 1
self_sets.__jit = 1
ints.__jit = 1
doubles.__jit = 1
run()
-- EXPECT: 2000
-- EXPECT: 1050
-- EXPECT: 15150	7575	15150
-- EXPECT: 2000
-- EXPECT: 1050
-- EXPECT: 15150	7575	15150
