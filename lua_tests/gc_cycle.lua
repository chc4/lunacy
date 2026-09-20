-- Cyclic garbage (a<->b and self references) must not keep objects alive
-- (mark-sweep handles cycles, unlike refcounting) and must not crash.
for i=1,200 do
  local a = {}
  local b = {}
  a.other = b
  b.other = a
  a.self = a
  collectgarbage("step")
end
collectgarbage("collect")
print("ok")
-- EXPECT: ok
