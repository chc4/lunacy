-- A machine's stack, an integer array kept in a field of the machine, passed
-- to small functions inlined into a loop, as an emulator's ops are: each loads
-- from the stack through its argument, and what a guard found of the field's
-- array kind tells those loads too. A lookup table of the machine's, loaded
-- from in the hash part and the array part, is stored into the stack. Once,
-- and in loops run often enough for JIT code.

local function new()
  local s = {}
  for i = 0, 256 do s[i] = 0 end
  return { wst = s, ORA = { [0] = 0, 1, 1, 1 } }
end

local function push(m, s, v)
  local p = (s[256] + 1) % 256
  s[p] = v
  s[256] = p
end

local function sub(m, s)
  local p = s[256]
  local v = (s[(p - 1) % 256] - s[p]) % 256
  p = (p - 1) % 256
  s[p] = v
  s[256] = p
end

local function ora(m, s)
  local p = s[256]
  local v = m.ORA[s[(p - 1) % 256] % 2 * 2 + s[p] % 2]
  p = (p - 1) % 256
  s[p] = v
  s[256] = p
end

local function run(m, n)
  local total = 0
  for i = 1, n do
    push(m, m.wst, i % 7)
    push(m, m.wst, i % 3)
    sub(m, m.wst)
    push(m, m.wst, i % 5)
    ora(m, m.wst)
    total = total + m.wst[m.wst[256]]
    if i == n - 3 then m.wst[0] = 0.5 end
  end
  return total
end

print(run(new(), 4))
print(run(new(), 500))
-- EXPECT: 3
-- EXPECT: 344
