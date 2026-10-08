-- Integer `%` by a constant: a positive power of two (a mask, its low bits,
-- for a negative left operand too), and by other constants and a negative
-- power of two (a floored remainder). Once, and in a loop run often enough for
-- JIT code.

local function mods(n)
  return n % 1, n % 2, n % 256, n % 65536, n % 1073741824, n % 3, n % -256, n % 6
end

local values = { 0, 1, 255, 256, 257, -1, -255, -256, -257, 65535, 65536, -65537, 2147483647, -2147483647 }
for i = 1, #values do
  print(values[i], mods(values[i]))
end

local function sum(from, to)
  local a, b, c, d = 0, 0, 0, 0
  for n = from, to do
    local w, x, y, z = n % 2, n % 256, n % 65536, n % -256
    a, b, c, d = a + w, b + x, c + y, d + z
  end
  return a, b, c, d
end
print(sum(-70000, 70000))
-- EXPECT: 0	0	0	0	0	0	0	0	0
-- EXPECT: 1	0	1	1	1	1	1	-255	1
-- EXPECT: 255	0	1	255	255	255	0	-1	3
-- EXPECT: 256	0	0	0	256	256	1	0	4
-- EXPECT: 257	0	1	1	257	257	2	-255	5
-- EXPECT: -1	0	1	255	65535	1073741823	2	-1	5
-- EXPECT: -255	0	1	1	65281	1073741569	0	-255	3
-- EXPECT: -256	0	0	0	65280	1073741568	2	0	2
-- EXPECT: -257	0	1	255	65279	1073741567	1	-1	1
-- EXPECT: 65535	0	1	255	65535	65535	0	-1	3
-- EXPECT: 65536	0	0	0	0	65536	1	0	4
-- EXPECT: -65537	0	1	255	65535	1073676287	1	-1	1
-- EXPECT: 2147483647	0	1	255	65535	1073741823	1	-1	1
-- EXPECT: -2147483647	0	1	1	1	1	2	-255	5
-- EXPECT: 70000	17850112	4587454464	-17850112
