local a = 3
local f = function()
    local second = function()
        print(a)
    end
    second()
end
a = 3
f()
