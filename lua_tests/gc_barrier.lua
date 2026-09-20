-- Interpreter-path table write barrier: store freshly-allocated (white) tables into a
-- long-lived (black) `root` mid-collection. A missed barrier would sweep the children out
-- from under root, making the reads below wrong (or crash under gc_sanitize).
local root = {}
collectgarbage("collect") -- settle the heap / run a full cycle

-- begin a fresh incremental cycle
for i=1,300 do collectgarbage("step") end

for i=1,150 do
  root[i] = { value = i * 3 }
  collectgarbage("step") -- interleave marking with the insert (barrier path)
end

collectgarbage("collect")

local sum = 0
for i=1,150 do sum = sum + root[i].value end
print(sum)
-- EXPECT: 33975
