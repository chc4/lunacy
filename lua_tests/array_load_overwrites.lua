-- An array load into its own table's or key's register (`t = t[k]`, `k =
-- t[k]`) that finds nil: a hole, or past the array's end, with and without an
-- `__index` table to look the key up in instead. The lookup past the nil reads
-- the table and key as they were before the load. With a register key and a
-- constant one; once, and in a loop run often enough for JIT code.

local function into_table(t, k)
  t = t[k]
  return t
end

local function into_key(t, k)
  k = t[k]
  return k
end

local function into_table_k(t)
  t = t[2]
  return t
end

local plain = { 10, nil, 30 }
local fallback = setmetatable({ 10, nil, 30 }, { __index = { [2] = 20, [4] = 40 } })

local function run(n)
  local sum = 0
  for _ = 1, n do
    for k = 1, 4 do
      sum = sum + (into_table(plain, k) or 0) + (into_key(plain, k) or 0)
      sum = sum + (into_table(fallback, k) or 0) + (into_key(fallback, k) or 0)
    end
    sum = sum + (into_table_k(plain) or 0) + (into_table_k(fallback) or 0)
  end
  return sum
end

print(run(1))
print(run(1000))
-- EXPECT: 300
-- EXPECT: 300000
