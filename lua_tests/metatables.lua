-- Tables' metatables with a table `__index`: the class pattern, inheritance
-- two and three deep, and a lookup going stale every way it can: a field of
-- the object's own shadowing the class's, setmetatable to another class, and
-- `__index` reassigned. An array's nil element and a global the environment
-- lacks are their `__index`'s too. getmetatable, `__metatable`, and
-- setmetatable's errors. Run interpreted, then with the functions JIT
-- compiled. See Note [Table metatables].
local Animal = {}
Animal.__index = Animal
function Animal.new(name) return setmetatable({name = name}, Animal) end
function Animal:speak() return self.name .. " makes a sound" end
function Animal:kind() return "animal" end

local Dog = setmetatable({}, Animal)
Dog.__index = Dog
function Dog.new(name) return setmetatable({name = name}, Dog) end
function Dog:speak() return self.name .. " barks" end

local Puppy = setmetatable({}, Dog)
Puppy.__index = Puppy
function Puppy.new(name) return setmetatable({name = name}, Puppy) end

local function chorus(list)
  local out = {}
  for i = 1, #list do out[#out + 1] = list[i]:speak() .. "/" .. list[i]:kind() end
  return table.concat(out, ", ")
end

local function stale(obj)
  local before = obj:kind()
  obj.kind = function() return "own" end
  local shadowed = obj:kind()
  obj.kind = nil
  setmetatable(obj, Animal)
  local swapped = obj:speak()
  local other = {kind = function() return "other" end}
  local saved = Animal.__index
  Animal.__index = other
  local reassigned = obj:kind()
  Animal.__index = saved
  return before, shadowed, swapped, reassigned, obj:kind()
end

local defaults = setmetatable({}, {__index = {10, 20, 30, x = "dx"}})
local function fallback(t)
  t[2] = 2
  return t[1], t[2], t[3], t[4], t.x
end

-- `__index` stored to in a loop, through the same store each time, then read
-- through the chain with no call between them, the object and the metatable
-- in the same registers throughout.
local function retarget(obj, mt, a, b)
  local out = {}
  for i = 1, 6 do
    if i % 2 == 1 then mt.__index = a else mt.__index = b end
    out[#out + 1] = obj.value
  end
  return table.concat(out, " ")
end
local retarget_mt = {}

-- A field read through the chain on one call, then from objects with it as
-- their own, or with it cleared to nil, on later ones.
local function own_field(o)
  return o.x
end
local own_mt = {__index = {x = "inherited"}}
local own_cleared = setmetatable({x = 1}, own_mt)
own_cleared.x = nil

local function globals()
  return undefined_global, another_undefined
end

local function run()
  print(chorus({Animal.new("cat"), Dog.new("rex"), Puppy.new("bit")}))
  print(stale(Puppy.new("pip")))
  print(fallback(defaults))
  print(retarget(setmetatable({}, retarget_mt), retarget_mt, {value = "A"}, {value = "B"}))
  local plain, own = setmetatable({}, own_mt), setmetatable({x = "own"}, own_mt)
  print(own_field(plain), own_field(own), own_field(own_cleared), own_field(plain), own_field(own))
  print(getmetatable(Dog.new("a")) == Dog, getmetatable({}), getmetatable(setmetatable({}, {__metatable = "locked"})))
  local ok, err = pcall(setmetatable, 1, {})
  local protected_ok, protected = pcall(setmetatable, setmetatable({}, {__metatable = true}), {})
  print(ok, err:find("table expected") ~= nil, protected_ok, protected:find("protected metatable") ~= nil)
  print(globals())
end
run()
setmetatable(_G, {__index = {undefined_global = "from G's __index"}})
print(globals())
chorus.__jit = 1
stale.__jit = 1
fallback.__jit = 1
retarget.__jit = 1
own_field.__jit = 1
globals.__jit = 1
run()
-- EXPECT: cat makes a sound/animal, rex barks/animal, bit barks/animal
-- EXPECT: animal	own	pip makes a sound	other	animal
-- EXPECT: 10	2	30	nil	dx
-- EXPECT: A B A B A B
-- EXPECT: inherited	own	inherited	inherited	own
-- EXPECT: true	nil	locked
-- EXPECT: false	true	false	true
-- EXPECT: nil	nil
-- EXPECT: from G's __index	nil
-- EXPECT: cat makes a sound/animal, rex barks/animal, bit barks/animal
-- EXPECT: animal	own	pip makes a sound	other	animal
-- EXPECT: 10	2	30	nil	dx
-- EXPECT: A B A B A B
-- EXPECT: inherited	own	inherited	inherited	own
-- EXPECT: true	nil	locked
-- EXPECT: false	true	false	true
-- EXPECT: from G's __index	nil
