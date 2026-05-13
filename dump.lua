require "io"

test_cases = {
    "do end",
    "local a = 6",
    "if true then print(1) end",
    "a = 5 return a",
    "local function foo() print('hi') end foo()",
    "local a, b, c = 1, 2, 3; return b, c, a;",
    "if true==true then a = 1 else a = 2 end return a",
    "local a = 1; local function foo(b) print(b, 'bye') end foo(a)",
    "local a = {4,5,6,7} print(a)",
    "local function foo(a) local counter = 0 for i = 1, a do counter = counter + i end return counter end print(foo(10000))",
    [==[print("hello " .. "goodbye")]==],
    "local function bar(a) return a+a end local function foo(a) for i=1, a do bar(a + i) end end foo(100000)",
    "local function foo(x,y) print(x,y) return 1,2 end local function fast() local a, b, c; a, b = foo(1,2) b, c = foo(3,4) a, b = foo(1,2) print(a, b, c) end fast()",
    "local function maybe(a) if a > 0 then print(1) else print(2) end end maybe(1) maybe(0)",
    "local a = {} function a:b() print(1) end a:b()",
    "local a = 1 print(a>0 and 1)",
    "local a = 1 print(a>0 and 1 or 2)",
    "local function fast() local t = {} t.a = 1 t.b = 2 print(t.a) for i = 1, 100 do t.c = t.a + t.b t.b = t.a + t.c end print(t.b) end fast()",
    [==[local function fast() local t = {} t.a = "test" print(t.a .. " post") t.a = 1 print(t.a + 1) end fast()]==],

    -- test an hkey wrong type through an aliased table
    -- emit epoch test on cached hkey, remove the dirty tracking stuff
    [==[t = {} local function fast() local x = t x.a = "1" local z = x.a .. x.a local y = t y.a = "2" local w = y.a .. y.a x.a = 1 print(y.a) print(y.a + 3) print(x.a + 4) print(z) print(w) end fast()]==],
    -- Local NativeFunction
    "function fast(p) local a = p(1.5) print(a) return a end assert(fast(math.ceil) == 2) assert(fast(math.floor) == 1)",
    "local function fast(p) local a = p(1.5) print(a) return a end assert(fast(math.ceil) == 2); fast.__jit = 1; assert(fast(math.floor) == 1)",
    -- HRef NativeFunction
    "function fast() local t = { print = print }; t.print('xyz'); end fast()",
}

for i,v in pairs(test_cases) do
    chunk = loadstring(v)
    dumped = string.dump(chunk)
    for i=0,#dumped do
        print(dumped:sub(i,i):byte())
    end

    dump_out = io.open("./dumped/dumped_"..i..".bin", "wb+")
    dump_out:write(dumped)
    dump_out:flush()
end
