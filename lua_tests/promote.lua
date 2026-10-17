-- jit.promote (where the Lua has none, a function returning its argument): a
-- machine whose code is a table of instructions, each an opcode and an operand,
-- run by a loop promoting its program counter and the opcode there, dispatching
-- through a table of functions that thread the program counter, as an
-- interpreter written in Lua does. Its code has branches (two successors), a
-- jump to a computed address (more successors than a promote tests), and an
-- instruction rewriting another's opcode while it runs. Then promotes of a
-- whole double, a string, a constant, a call taking all its results, and of
-- more values than a promote tests. Once, and in loops run often enough for
-- JIT code.

local promote = jit and jit.promote or function(x) return x end

local ADD, BRANCH, COMPUTED, PATCH, HALT = 1, 2, 3, 4, 5

local ops = {}
-- acc += operand
ops[ADD] = function(code, pc, acc) return pc + 1, acc + code[pc][2] end
-- to the operand's address if acc is odd, else on
ops[BRANCH] = function(code, pc, acc)
  if acc % 2 == 1 then return code[pc][2], acc end
  return pc + 1, acc
end
-- to address 6 + acc % operand
ops[COMPUTED] = function(code, pc, acc) return 6 + acc % code[pc][2], acc + 1 end
-- the instruction at the operand's address becomes an ADD, once acc is past 20
ops[PATCH] = function(code, pc, acc)
  if acc > 20 then code[code[pc][2]][1] = ADD end
  return pc + 1, acc
end

local function program()
  local code = {
    { ADD, 1 },        -- 1
    { BRANCH, 4 },     -- 2
    { ADD, 2 },        -- 3
    { PATCH, 5 },      -- 4
    { COMPUTED, 12 },  -- 5, an ADD of 12 once patched
  }
  -- 6 .. 17: computed targets, each adding its index and jumping back
  for i = 6, 17 do code[i] = { ADD, i } end
  code[18] = { HALT, 0 }
  return code
end

local function run(code, steps)
  local pc, acc = 1, 0
  for _ = 1, steps do
    pc = promote(pc)
    local op = promote(code[pc][1])
    if op == HALT then return acc, pc end
    pc, acc = ops[op](code, pc, acc)
    -- the computed targets fall back to the start
    if pc > 5 and pc < 18 and code[pc - 1] and pc - 1 > 5 then pc = 1 end
  end
  return acc, pc
end

print(run(program(), 50))
local total = 0
for i = 1, 300 do
  local acc = run(program(), 40 + i % 7)
  total = total + acc
end
print(total)

-- A whole double, a string, a constant, and all of a call's results; and a
-- promote in a function of its own, so each call's version of it starts with no
-- promoted value and tests the values in turn: more of them than a version tests.
local function pick(v) return promote(v) + 0 end
local function others(n)
  local sum = 0
  for i = 1, n do
    sum = sum + promote((i % 3) / 1) + promote(7) + #promote("abc") + pick(i % 12)
  end
  return sum, promote(n % 5)
end
print(others(10))
print(others(500))
-- EXPECT: 54	6
-- EXPECT: 8365
-- EXPECT: 165	0
-- EXPECT: 8243	0
