-- Exercise the write barrier on the *native JIT* code path. `root` is a global, so
-- it's permanently reachable via _G and gets marked black by the collector. The
-- JIT-compiled `insert` stores freshly-allocated (white) subtables into that black
-- `root` via SETTABLE while collection is in progress -- exactly the case the backward
-- write barrier exists for. If the JIT path missed the barrier, `root` would stay black
-- pointing at a white child, the child would be swept, and reading it back below would
-- yield the wrong sum (or panic "value is dead" under gc_sanitize).
root = {}

function insert(base, count)
  local r = root
  for i = 1, count do
    r[base + i] = { base + i } -- SETTABLE into the long-lived (black) root
  end
end

insert(0, 1)      -- warmup: run the loop body once so its LBBV block exists to compile
insert.__jit = 1  -- force native JIT compilation of `insert`
collectgarbage("collect")

for batch = 0, 9 do
  insert(batch * 1000, 1000) -- JIT-compiled SETTABLEs into the black root
  collectgarbage("step")     -- interleave marking with the mutations (barrier path)
end
collectgarbage("collect")

local total = 0
for k = 1, 10000 do
  total = total + root[k][1]
end
print(total)
-- EXPECT: 50005000
