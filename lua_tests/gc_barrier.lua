-- Write-barrier stress: keep a long-lived table `root` that the incremental
-- collector will have already marked (blackened), then store freshly allocated
-- tables into it *while a collection is in progress*. Without a correct write
-- barrier those fresh (white) children would be swept out from under a black
-- parent and the reads below would be wrong (or crash under gc_sanitize).
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
