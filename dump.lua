require "io"

test_cases = {
    "do end",
    "local a = 6",
    "local function foo() print('hi') end",
    "a = 1 for i=1,10 do print(a) end",
    "if true then print(1) end",
    "a = 3 return a",
}

for i,v in pairs(test_cases) do
    chunk = loadstring(v)
    dumped = string.dump(chunk)
    for i=0,#dumped do
        print(dumped:sub(i,i):byte())
    end

    dump_out = io.open("./dumped_"..i..".bin", "wb")
    dump_out:write(dumped)
    dump_out:flush()
end

a = 0
do
    function foo()
        b = 2
    end
    foo()
end
print(b)
