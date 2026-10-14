-- Objects of a class, each with a metatable of its own whose `__index` is the
-- class, as havlak's are: a field of the object and a method of the class,
-- each found through its own hash key, never one for the other.
local Vector = {}

local function alloc(n)
  local t = {}
  t.n = n
  return t
end

function Vector.new(size)
  local obj = { storage = alloc(size or 2), first = 1, last = 1 }
  return setmetatable(obj, {__index = Vector})
end

function Vector.with(elem)
  local v = Vector.new(1)
  v:append(elem)
  return v
end

function Vector:append(elem)
  if self.last > self.storage.n then
    local grown = alloc(2 * self.storage.n)
    for i = 1, self.storage.n do
      grown[i] = self.storage[i]
    end
    self.storage = grown
  end
  self.storage[self.last] = elem
  self.last = self.last + 1
end

function Vector:size()
  return self.last - self.first
end

function Vector:each(fn)
  for i = self.first, self.last - 1 do
    fn(self.storage[i])
  end
end

local function run(n)
  local vs = {}
  for i = 1, n do
    local v = (i % 3 == 0) and Vector.with(i) or Vector.new(i % 4 + 1)
    for j = 1, i % 7 do
      v:append(j * i)
    end
    vs[#vs + 1] = v
  end
  local total, count = 0, 0
  for _, v in ipairs(vs) do
    count = count + v:size()
    v:each(function(e) total = total + e end)
  end
  return count, total
end

print(run(10))
print(run(100))
for _ = 1, 20 do run(50) end
print(run(200))
-- EXPECT: 30	379
-- EXPECT: 330	41478
-- EXPECT: 664	166242
