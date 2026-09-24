-- Phase shifts: one loop runs hot through phases that each take guard sides
-- the earlier phases never did, so code compiled during one phase meets new
-- paths in the next (thunks forced after their blocks were compiled). The
-- phases are inline in one function, as calls aren't specialized, and each
-- runs the loop far past the JIT's hotness threshold. Keys stay small: the
-- array part isn't sparse.

local EXPECT_CKSUM = 17324800
local N = 64       -- keys per round
local ROUNDS = 200 -- rounds per phase
-- Per phase: the step and offset of its keys, and what it adds to each value.
local STEPS   = { 1,      1,  0.5, 1,   1 }
local OFFSETS = { 0, -2 * N,    0, 0,   0 }
local ADDS    = { 1,      1,    1, 0.5, 1 }

local function inner_iter()
  local t = {}
  for i = 1, N do t[i] = i end
  local sum = 0
  for p = 1, #STEPS do
    -- Integer keys in the array part; below it, in the hash part; integers
    -- every other key; fractional values; back to the first.
    local step, offset, add = STEPS[p], OFFSETS[p], ADDS[p]
    for _ = 1, ROUNDS do
      for i = 1, N do
        local k = i * step + offset
        local v = t[k]
        if v ~= nil then
          sum = sum + v
        else
          v = 0
        end
        t[k] = v + add
      end
    end
  end
  if sum ~= EXPECT_CKSUM then
    io.write("bad checksum: " .. sum .. " vs " .. EXPECT_CKSUM)
    os.exit(1)
  end
end

function run_iter(n)
  for i = 1, n do
    inner_iter()
  end
end
