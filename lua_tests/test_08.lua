-- EXPECT: 1	bye
local a = 1; local function foo(b) print(b, 'bye') end foo(a)