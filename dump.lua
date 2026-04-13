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
    "local function fast() local t = {} t.a = 1 t.b = 2 t.c = t.a + 1 t.b = t.a + t.c print(t.b) end fast()",
    [==[local function fast() local t = {} t.a = "test" print(t.a .. " post") t.a = 1 print(t.a + 1) end fast()]==],
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
