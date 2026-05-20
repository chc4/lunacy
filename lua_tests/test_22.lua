-- EXPECT: 2
-- EXPECT: 1
local function fast(p) local a = p(1.5) print(a) return a end assert(fast(math.ceil) == 2); fast.__jit = 1; assert(fast(math.floor) == 1)