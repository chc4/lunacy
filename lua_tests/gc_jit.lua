-- Exercise the GC on the *native JIT* code path. `build` allocates a large live
-- table of subtables, mutates it, and reads it back -- all opcodes the block
-- specializer implements. We warm it up once (to populate the LBBV blocks), then
-- use the `__jit` magic intrinsic to force native compilation of those blocks, so
-- the subsequent calls run table allocation / mutation / GC safepoints through the
-- JIT. Under gc_stress + gc_sanitize this catches any write-barrier miss on the
-- JIT path (a reclaimed-but-live object would panic "value is dead").
local function build(n)
  local root = {}
  for i = 1, n do
    root[i] = { i, i * 2, i * 3 }
  end
  local s = 0
  for i = 1, n do
    s = s + root[i][1] + root[i][2] + root[i][3]
  end
  return s
end

build(50)        -- warmup: saturate the LBBV blocks so __jit has blocks to compile
build.__jit = 1  -- force native JIT compilation of build's blocks

local total = 0
for k = 1, 3 do
  total = total + build(800)
  collectgarbage("step")
end
collectgarbage("collect")
print(total)
-- EXPECT: 5767200
