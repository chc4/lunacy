require "io"

testcases = {...}
for _,v in pairs(testcases) do
    if v:sub(-4) == ".lua" then
        print("> process", v)
        testcase = io.open(v, "rb")
        testcase_dump = io.open(v:sub(0,-5)..".bin", "wb+")
        testcase_bytecode = loadstring(testcase:read("*all"))
        if testcase_bytecode == nil then
            error("couldn't compile")
        end
        testcase_dump:write(string.dump(testcase_bytecode))
        testcase_dump:flush()
        testcase_dump:close()
    end
end
