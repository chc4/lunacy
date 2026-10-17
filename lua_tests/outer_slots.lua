-- An inlined callee reads an upvalue open onto its caller's local from that slot. Writes to the
-- local by either are seen by both, through a nested inlined call too.
local function run(n)
  local k, hits = 3, 0
  local function get(x) return x + k end
  local function bump() hits = hits + 1 end
  local function nested(x) return get(x) * 2 end
  local s = 0
  for i = 1, n do
    s = s + get(i)
    if i % 7 == 0 then k = k + 1 end
    bump()
    s = s + nested(i) + hits
  end
  return s, k, hits
end

print(run(100))
print(run(1000))
run.__jit = 1
print(run(1000))
-- EXPECT: 23123	17	100
-- EXPECT: 2224071	145	1000
-- EXPECT: 2224071	145	1000
