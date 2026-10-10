-- The code after a call reached in two contexts that differ only in the call's own frame is
-- one version: a call whose argument is an integer one time and a string the next, and a
-- generic for whose iterator gets an integer control value one time and a string the next.
-- Run by the interpreter, then in JIT code.

local versions = jit and jit.versions or function() return 1 end

local function one(_) return 1 end

local function after_call(x)
  one(x == 1 and 1 or "str")
  local n = versions()
  return n
end

local function next_two(_, control)
  if control ~= 2 then return 2 end
end

local function after_for(x)
  local n = 0
  for _ in next_two, nil, x == 1 and 0 or "str" do
    n = n + versions()
  end
  return n
end

print(after_call(1), after_call(2), after_for(1), after_for(2))
after_call.__jit = 1
after_for.__jit = 1
print(after_call(1), after_call(2), after_for(1), after_for(2))
-- EXPECT: 1	1	1	1
-- EXPECT: 1	1	1	1
