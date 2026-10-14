-- A field an integer in one table and a double in another: where both reach
-- the same code its hash key is a `Number`, whose loads leave the encoding to
-- the uses that test it. See Note [Field types].
local function bump(t)
  t.last = t.last + 1
  return t.last
end
bump.__jit = 1
local i, d = { last = 0 }, { last = 0.5 }
i.last = i.last + 0
print(bump(i), bump(d), bump(i), bump(d))
-- EXPECT: 1	1.5	2	2.5

-- As a key: a whole double field narrowed, an integer one kept.
local function store(t, v)
  t.items[t.last] = v
  return t.items[t.last]
end
store.__jit = 1
local a, b = { last = 1, items = {} }, { last = 2, items = {} }
b.last = b.last + 0
print(store(a, "a"), store(b, "b"), store(a, "c"), store(b, "d"))
-- EXPECT: a	b	c	d
