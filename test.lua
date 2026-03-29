local a = 3
local first = function()
    local second = function()
        print("second", a)
        return 2
    end
    local v = second()
    print("first", v)
    return v
end
a = 3
local c = first()
print(c)
return c
