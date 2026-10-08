-- Whole constants stored into an array part, which are stored as integers:
-- arrays filled with a constant, and from a local holding one, then given
-- computed integers and read back; next to stores of a negative zero and of a
-- fractional constant, which aren't whole. What's read decides what the code does with
-- it, so an array read as of a kind it doesn't have goes wrong. Once, and in
-- loops run often enough for JIT code.

local function fill(n)
  local t, u = {}, {}
  local z = 0
  for i = 1, n do
    t[i] = 0
    u[i] = z
  end
  return t, u
end

local function run(n)
  local t, u = fill(n)
  for i = 1, n do
    t[i] = (t[i] + i * 7) % 256
    u[i] = u[i] + i
  end
  local sum, odd = 0, 0
  for i = 1, n do
    sum = sum + t[i] + u[i]
    if t[i] % 2 == 1 then odd = odd + 1 end
  end
  -- luac folds a constant -0 to 0: a negative zero is computed.
  local zero = 0
  local signs = { 0, 0 }
  signs[1] = -zero
  signs[2] = 0.5
  return sum, odd, tostring(signs[1]), signs[2] * 2, 1 / signs[1]
end

print(run(10))
print(run(1000))
-- EXPECT: 440	5	-0	1	-inf
-- EXPECT: 627104	500	-0	1	-inf
