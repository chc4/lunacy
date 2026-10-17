-- Two closures share a local's cell once it is closed: a store through one is seen through the
-- other, whatever the caller forgot of the closures before the close, even its type. `just
-- golden-conservative-every` forgets at each yield of its specializing in turn.
local function run(n)
  local s = 0
  for i = 1, n do
    local set, get
    do
      local x = {k = i}
      get = function() return x end
      set = function(v) x = v end
    end
    local before = get()
    set(i * 7)
    s = s + get()
  end
  return s
end

print(run(10))
print(run(300))
run.__jit = 1
print(run(300))
-- EXPECT: 385
-- EXPECT: 316050
-- EXPECT: 316050
