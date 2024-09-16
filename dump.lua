require "io"

test_cases = {
    "do end",
    "a = 6",
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
