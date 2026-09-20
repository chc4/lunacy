-- Cyclic garbage (a<->b and self references) must be reclaimed: mark-sweep handles
-- cycles, unlike refcounting. Weigh the heap before and after -- it must return to the
-- baseline, proving the unreachable cycles were actually freed (not leaked).
collectgarbage("collect")
local base = collectgarbage("count")

for i = 1, 20000 do
  local a = {}
  local b = {}
  a.other = b
  b.other = a
  a.self = a
end

collectgarbage("collect")
local after = collectgarbage("count")

if after < base + 50 then
  print("cycles reclaimed")
else
  print("FAIL leaked base=" .. base .. " after=" .. after)
end
-- EXPECT: cycles reclaimed
