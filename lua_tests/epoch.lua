local function use(a)
    print(a)
end

local function foo(t)
    use(t.a)
    return t.a
end

local function bar(t)
    foo(t)
    t.b = 1
    foo(t)
end


-- EXPECT: table: 0x584f896a5af0
-- EXPECT: table: 0x584f896a5af0
-- EXPECT: table: 0x584f896a4670
-- EXPECT: table: 0x584f896a4670
-- EXPECT: nil
-- EXPECT: nil
bar({a = {}})
bar({b = 1, a = {}})
bar({})
