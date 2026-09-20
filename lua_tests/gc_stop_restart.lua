-- collectgarbage("stop") disables automatic collection; "restart" re-enables it.
-- Program semantics must be unaffected either way.
collectgarbage("stop")
local live = {}
for i=1,100 do
  live[i] = i
  local junk = { i, i } -- would normally trigger stepping; GC is off
end
collectgarbage("restart")
collectgarbage("collect")
local sum = 0
for i=1,100 do sum = sum + live[i] end
print(sum)
-- EXPECT: 5050
