-- Dynamically constructed (owned) strings are GC-managed; they must survive a
-- collection when still referenced from a live table.
local parts = {}
for i=1,50 do
  parts[i] = "s" .. i
end
collectgarbage("collect")
local total = 0
for i=1,50 do
  total = total + #parts[i]
end
print(total)
-- EXPECT: 141
