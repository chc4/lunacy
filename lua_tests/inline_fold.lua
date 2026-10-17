-- An inlined call is as if its code were in its caller: what it returns folds
-- into what the caller computes from it.

local function a() return 3 end
local function b() return 1 + a() end
local function c(x) return x * 2 end

local s = 0
for i = 1, 1000 do
  s = s + b() + c(i)
end
print(s)
-- EXPECT: 1005000
