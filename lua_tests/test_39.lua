-- EXPECT: 1
-- EXPECT: 3
-- EXPECT: 5
-- EXPECT: 7	8
-- FAILS: after a MULTRET-consuming call (print(useboth())), do_return truncates
-- the stack to the returned-value count, under-sizing the caller frame, so a
-- later instruction indexes past the live stack (vm.rs do_return / MOVE).
local function two() return 1, 2 end
local x = two()
print(x)
local function useboth() local a, b = two(); return a + b end
print(useboth())
local function id(v) return v end
print(id(id(id(5))))
local function pick2() return 7, 8, 9 end
local m, n = pick2()
print(m, n)
