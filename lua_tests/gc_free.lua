-- Assert the collector actually *reclaims* memory (a no-op GC would fail this).
-- The live count must grow while a large structure is held, then return to near the
-- baseline once it is unreachable and collected.
collectgarbage("collect")
local base = collectgarbage("count")

local hold = {}
for i = 1, 50000 do
  hold[i] = { i, i, i }
end
local peak = collectgarbage("count")

hold = nil
collectgarbage("collect")
local after = collectgarbage("count")

-- grew a lot while alive, and came back down to ~baseline after freeing
if peak > base + 500 and after < base + 100 then
  print("reclaimed")
else
  print("FAIL base=" .. base .. " peak=" .. peak .. " after=" .. after)
end
-- EXPECT: reclaimed
