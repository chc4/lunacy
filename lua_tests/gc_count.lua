-- collectgarbage("count") reports live memory in Kbytes. The globals table is
-- always live, so it is strictly positive after a full collection.
collectgarbage("collect")
if collectgarbage("count") > 0 then
  print(1)
else
  print(0)
end
-- EXPECT: 1
