-- A small function inlined into a loop, passed a table whose fields the caller
-- knows, the last of its hash keys: it reads a field of it, then sets its
-- parameter to another table, so the hash keys it was passed go, leaving fewer
-- than its caller had. The caller's past them are free when it returns, and
-- the caller reads the table's fields again after each call. Once, and in
-- loops run often enough for JIT code.

local function take(t, k)
  local v = t.e + k
  t = { e = 0 }
  t.e = t.e + v
  return t.e
end

local function run(n)
  local u = { a = 1, b = 2, c = 3, d = 4, e = 5 }
  local total = 0
  for i = 1, n do
    total = total + u.a + u.b + u.c + u.d + u.e
    total = total + take(u, i % 3)
    total = total + u.a + u.e
    u.e = u.e + 1
  end
  return total, u.e
end

print(run(4))
print(run(500))
-- EXPECT: 126	9
-- EXPECT: 387751	505
