-- An inlined callee's upvalues open onto its caller's locals hold what the caller last wrote to
-- them, and the caller sees what the callee stores, in JIT code holding the locals in registers.
local function run(n)
  local hits, other = 0, 0
  local function bump()
    other = other + 1
    local seen = hits
    hits = hits + 1
    return seen
  end
  local s = 0
  for i = 1, n do
    hits = hits + i
    s = s + bump()
    s = s + hits
  end
  return s, hits, other
end

print(run(10))
print(run(200))
run.__jit = 1
print(run(200))
-- EXPECT: 540	65	10
-- EXPECT: 2746800	20300	200
-- EXPECT: 2746800	20300	200
