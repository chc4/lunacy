-- assert as a statement, passing and failing, with a message and with the default one, caught
-- by pcall; and an assert whose results are used. Run by the interpreter, then in JIT code.

local function check(x, limit)
  assert(x >= 0, "negative")
  assert(x < limit)
  return x * 2
end

local function kept(x)
  local v, m = assert(x, "missing")
  return v, m
end

local function run(n, limit)
  local sum, negative, failed = 0, 0, 0
  for i = -3, n do
    local ok, r = pcall(check, i, limit)
    if ok then
      sum = sum + r
    elseif r == "negative" then
      negative = negative + 1
    elseif r == "assertion failed!" then
      failed = failed + 1
    end
  end
  local ok1, a, b = pcall(kept, 7)
  local ok2, e = pcall(kept, false)
  return sum, negative, failed, ok1, a, b, ok2, e
end

print(run(10, 8))
run.__jit = 1
check.__jit = 1
kept.__jit = 1
print(run(10, 8))
print(run(100, 50))
-- EXPECT: 56	3	3	true	7	missing	false	missing
-- EXPECT: 56	3	3	true	7	missing	false	missing
-- EXPECT: 2450	3	51	true	7	missing	false	missing
