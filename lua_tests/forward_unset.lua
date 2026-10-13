-- A stack in a table, its pointer in an element past it, as uxn's: each push
-- an inlined call storing the pointer from a temporary, the next call loading
-- it into the slot that temporary was, where the stored value still is, and
-- reading it there, each iteration of a loop compiled. The stack is a field
-- jit.learn learns, so the loads know its array's kind.

local learn = jit and jit.learn or function(t) return t end

local function push(s, v)
  local q = (s[9] + 1) % 8
  s[q + 1] = v
  s[9] = q
  return v
end

local function top(s, k)
  local p = s[9]
  return s[p + 1] * 2 + p + k
end

local function run(n, m)
  learn(m)
  local s, push, top = m.s, m.push, m.top
  local sum = 0
  for i = 1, n do
    push(s, i)
    sum = sum + top(s, 1)
  end
  return sum, s[9]
end

local function show(n)
  local sum, p = run(n, { s = { 0, 0, 0, 0, 0, 0, 0, 0, 0 }, push = push, top = top })
  print(sum .. " " .. p)
end

show(10)
show(3000)
-- EXPECT: 151 2
-- EXPECT: 9016500 0
