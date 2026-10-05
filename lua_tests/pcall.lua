-- pcall: a call's results after true, or false and the error raised in it,
-- however deep: by error (with any value), assert, a native, or calling a
-- non-function. Nested calls unwind to the innermost; a closure made in an
-- unwound frame keeps its upvalues; pcall returned as a tail call. Run
-- interpreted, then with the functions JIT compiled. See Note [Errors].
local function sum(a, b) return a + b, a * b end
local function deep(n, v)
  if n == 0 then error(v, 0) end
  return deep(n - 1, v) + 1
end
local kept
local function capture(x)
  local secret = x * 2
  kept = function() return secret end
  error({code = x})
end
local function nested()
  local ok, err = pcall(deep, 3, "inner")
  return ok, err, "after"
end
local function tail(f, ...) return pcall(f, ...) end
local function loop(n)
  local caught = 0
  for i = 1, n do
    local ok = pcall(deep, i % 3, i)
    if not ok then caught = caught + 1 end
  end
  return caught
end
local function run()
  print(pcall(sum, 2, 3))
  print(pcall(error, "plain"))
  print(pcall(deep, 5, "five deep"))
  local ok, err = pcall(capture, 21)
  print(ok, type(err), err.code, kept())
  print(nested())
  print(pcall(assert, false, "asserted"), pcall(assert, nil))
  print(pcall(assert, 1, 2))
  print(pcall(string.find, "x", "["))
  print(pcall(nil))
  print(pcall(error))
  print(tail(sum, 4, 5))
  print(tail(deep, 1, "tail error"))
  print(loop(30))
end
run()
sum.__jit = 1
deep.__jit = 1
capture.__jit = 1
nested.__jit = 1
tail.__jit = 1
loop.__jit = 1
run()
-- EXPECT: true	5	6
-- EXPECT: false	plain
-- EXPECT: false	five deep
-- EXPECT: false	table	21	42
-- EXPECT: false	inner	after
-- EXPECT: false	false	assertion failed!
-- EXPECT: true	1	2
-- EXPECT: false	malformed pattern (missing ']')
-- EXPECT: false	attempt to call a nil value
-- EXPECT: false	nil
-- EXPECT: true	9	20
-- EXPECT: false	tail error
-- EXPECT: 30
-- EXPECT: true	5	6
-- EXPECT: false	plain
-- EXPECT: false	five deep
-- EXPECT: false	table	21	42
-- EXPECT: false	inner	after
-- EXPECT: false	false	assertion failed!
-- EXPECT: true	1	2
-- EXPECT: false	malformed pattern (missing ']')
-- EXPECT: false	attempt to call a nil value
-- EXPECT: false	nil
-- EXPECT: true	9	20
-- EXPECT: false	tail error
-- EXPECT: 30
