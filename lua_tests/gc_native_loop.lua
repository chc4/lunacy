-- A loop whose only allocation is a native call (table.new) still collects:
-- its block ends in a GC safepoint. Without one, every table would stay live.
require("table.new")
local function churn(n)
  for i = 1, n do
    local t = table.new(16, 0)
    t[1] = i
  end
end
churn(10)
churn.__jit = 1
churn(200000)
print(collectgarbage("count") < 4096)
-- EXPECT: true
