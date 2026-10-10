-- A global table of functions, loaded and called by small functions inlined
-- into a loop, as code calls `math.floor`: what a guard finds of the global
-- and its field, and of a global function, holds until something stores
-- into it. The global is set to
-- another table, directly, through the environment in a register, and by a
-- call of a function that sets it; and the field is set to another function.
-- What's called decides what's summed. Once, and in loops run often enough for
-- JIT code.

lib = { f = function(x) return x + 1 end }
local function inc(x) return x + 1 end
local function triple(x) return x * 3 end
gfun = inc
local plain = lib
local doubled = { f = function(x) return x * 2 end }
local function swap() lib = plain; gfun = inc end
local env = _G

local function step(x) return lib.f(x) + gfun(x) end
local function floored(x) return math.floor(x / 2) end

local function run(n)
  local total = 0
  for i = 1, n do
    total = total + step(i) + floored(i)
    if i % 7 == 0 then lib = doubled; gfun = triple end
    total = total + step(i)
    if i % 11 == 0 then env.lib = plain; env.gfun = inc end
    total = total + step(i)
    if i % 13 == 0 then lib = doubled; gfun = triple; swap() end
    if i % 19 == 0 then env.gfun = triple end
    total = total + step(i)
    if i % 17 == 0 then doubled.f = function(x) return x - 1 end end
    total = total + step(i) + floored(i + 1)
  end
  lib, gfun = plain, inc
  return total
end

print(run(4))
print(run(500))
-- EXPECT: 150
-- EXPECT: 2063730
