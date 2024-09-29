require "io"

test_cases = {
    "do end",
    "local a = 6",
    "if true then print(1) end",
    "a = 5 return a",
    "local function foo() print('hi') end foo()",
    "local a, b, c = 1, 2, 3; return b, c, a;",
    "if true==true then a = 1 else a = 2 end return a",
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
