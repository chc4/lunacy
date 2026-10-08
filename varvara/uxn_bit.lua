-- The Uxn CPU of uxn.lua, written with the bit library rather than arithmetic:
-- it wraps stack pointers, addresses and results by masking, makes and splits
-- shorts by shifting, and computes AND, ORA, EOR and SFT by the operations
-- themselves. Its machines are uxn.lua's, and run the same.
--
-- It needs LuaJIT's `bit` library (as lunacy has), or Luau's `bit32`, as a
-- global.

local bit = bit or bit32
local band, bor, bxor, lshift, rshift = bit.band, bit.bor, bit.bxor, bit.lshift, bit.rshift
local floor = math.floor

local M = {}

-- lunacy's `jit.promote`, where the Lua has it. See `eval`.
local promote = jit and jit.promote

local function signed(byte)
  return byte - lshift(band(byte, 0x80), 1)
end

-- A new machine with zeroed memory. `dei(port)` reads a device port, and
-- `deo(port, value)` writes one, as `set_devices` sets them.
function M.new()
  local ram, wst, rst = {}, {}, {}
  for i = 0, 65535 do ram[i] = 0 end
  for i = 0, 256 do wst[i], rst[i] = 0, 0 end
  local dei, deo

  -- Each operation, without and with keep (`k` 0 or 1), on its stack `s`, with
  -- the other stack `o` for the operations moving a value onto it, and `pc`,
  -- the program counter past its instruction. It returns the program counter
  -- to go on from, or nothing to stop the machine. The program counter is a
  -- local of `eval`, threaded through the operations, rather than an upvalue
  -- they share: setting one, a closed cell, is a store out of line in lunacy,
  -- and a call that may have set one forgets what the caller knew of every
  -- upvalue.
  local ops = {}

  -- A short's result written as the top two bytes of `s` below pointer `p`.
  local function put2(s, p, v)
    s[p] = band(v, 255)
    s[band(p - 1, 255)] = band(rshift(v, 8), 255)
  end

  ops[0x01] = function(k) return function(s, o, pc) -- INC
    local p = s[256]
    local t = s[p]
    p = band(p + k, 255)
    s[p] = band(t + 1, 255)
    s[256] = p
    return pc
  end end
  ops[0x21] = function(k) return function(s, o, pc) -- INC2
    local p = s[256]
    local t = bor(lshift(s[band(p - 1, 255)], 8), s[p])
    p = band(p + 2 * k, 255)
    put2(s, p, band(t + 1, 65535))
    s[256] = p
    return pc
  end end
  ops[0x02] = function(k) return function(s, o, pc) -- POP
    s[256] = band(s[256] + k - 1, 255)
    return pc
  end end
  ops[0x22] = function(k) return function(s, o, pc) -- POP2
    s[256] = band(s[256] + 2 * k - 2, 255)
    return pc
  end end
  ops[0x03] = function(k) return function(s, o, pc) -- NIP
    local p = s[256]
    local t = s[p]
    p = band(p + 2 * k - 1, 255)
    s[p] = t
    s[256] = p
    return pc
  end end
  ops[0x23] = function(k) return function(s, o, pc) -- NIP2
    local p = s[256]
    local t, tl = s[band(p - 1, 255)], s[p]
    p = band(p + 4 * k - 2, 255)
    s[p], s[band(p - 1, 255)] = tl, t
    s[256] = p
    return pc
  end end
  ops[0x04] = function(k) return function(s, o, pc) -- SWP
    local p = s[256]
    local t, n = s[p], s[band(p - 1, 255)]
    p = band(p + 2 * k, 255)
    s[p], s[band(p - 1, 255)] = n, t
    s[256] = p
    return pc
  end end
  ops[0x24] = function(k) return function(s, o, pc) -- SWP2
    local p = s[256]
    local t1, t0, n1, n0 = s[band(p - 1, 255)], s[p], s[band(p - 3, 255)], s[band(p - 2, 255)]
    p = band(p + 4 * k, 255)
    s[band(p - 1, 255)], s[p], s[band(p - 3, 255)], s[band(p - 2, 255)] = n1, n0, t1, t0
    s[256] = p
    return pc
  end end
  ops[0x05] = function(k) return function(s, o, pc) -- ROT
    local p = s[256]
    local t, n, l = s[p], s[band(p - 1, 255)], s[band(p - 2, 255)]
    p = band(p + 3 * k, 255)
    s[p], s[band(p - 1, 255)], s[band(p - 2, 255)] = l, t, n
    s[256] = p
    return pc
  end end
  ops[0x25] = function(k) return function(s, o, pc) -- ROT2
    local p = s[256]
    local t1, t0 = s[band(p - 1, 255)], s[p]
    local n1, n0 = s[band(p - 3, 255)], s[band(p - 2, 255)]
    local l1, l0 = s[band(p - 5, 255)], s[band(p - 4, 255)]
    p = band(p + 6 * k, 255)
    s[band(p - 1, 255)], s[p] = l1, l0
    s[band(p - 3, 255)], s[band(p - 2, 255)] = t1, t0
    s[band(p - 5, 255)], s[band(p - 4, 255)] = n1, n0
    s[256] = p
    return pc
  end end
  ops[0x06] = function(k) return function(s, o, pc) -- DUP
    local p = s[256]
    local t = s[p]
    p = band(p + k + 1, 255)
    s[p], s[band(p - 1, 255)] = t, t
    s[256] = p
    return pc
  end end
  ops[0x26] = function(k) return function(s, o, pc) -- DUP2
    local p = s[256]
    local t1, t0 = s[band(p - 1, 255)], s[p]
    p = band(p + 2 * k + 2, 255)
    s[band(p - 1, 255)], s[p] = t1, t0
    s[band(p - 3, 255)], s[band(p - 2, 255)] = t1, t0
    s[256] = p
    return pc
  end end
  ops[0x07] = function(k) return function(s, o, pc) -- OVR
    local p = s[256]
    local t, n = s[p], s[band(p - 1, 255)]
    p = band(p + 2 * k + 1, 255)
    s[p], s[band(p - 1, 255)], s[band(p - 2, 255)] = n, t, n
    s[256] = p
    return pc
  end end
  ops[0x27] = function(k) return function(s, o, pc) -- OVR2
    local p = s[256]
    local t1, t0, n1, n0 = s[band(p - 1, 255)], s[p], s[band(p - 3, 255)], s[band(p - 2, 255)]
    p = band(p + 4 * k + 2, 255)
    s[band(p - 1, 255)], s[p] = n1, n0
    s[band(p - 3, 255)], s[band(p - 2, 255)] = t1, t0
    s[band(p - 5, 255)], s[band(p - 4, 255)] = n1, n0
    s[256] = p
    return pc
  end end

  -- The comparisons: a byte flag from the top two bytes, or shorts.
  local function compare(test)
    return function(k) return function(s, o, pc)
      local p = s[256]
      local t, n = s[p], s[band(p - 1, 255)]
      p = band(p + 2 * k - 1, 255)
      s[p] = test(n, t) and 1 or 0
      s[256] = p
      return pc
    end end,
    function(k) return function(s, o, pc)
      local p = s[256]
      local t = bor(lshift(s[band(p - 1, 255)], 8), s[p])
      local n = bor(lshift(s[band(p - 3, 255)], 8), s[band(p - 2, 255)])
      p = band(p + 4 * k - 3, 255)
      s[p] = test(n, t) and 1 or 0
      s[256] = p
      return pc
    end end
  end
  ops[0x08], ops[0x28] = compare(function(n, t) return n == t end) -- EQU
  ops[0x09], ops[0x29] = compare(function(n, t) return n ~= t end) -- NEQ
  ops[0x0a], ops[0x2a] = compare(function(n, t) return n > t end) -- GTH
  ops[0x0b], ops[0x2b] = compare(function(n, t) return n < t end) -- LTH

  ops[0x0c] = function(k) return function(s, o, pc) -- JMP
    local p = s[256]
    local t = s[p]
    s[256] = band(p + k - 1, 255)
    pc = band(pc + signed(t), 65535)
    return pc
  end end
  ops[0x2c] = function(k) return function(s, o, pc) -- JMP2
    local p = s[256]
    local t = bor(lshift(s[band(p - 1, 255)], 8), s[p])
    s[256] = band(p + 2 * k - 2, 255)
    pc = t
    return pc
  end end
  ops[0x0d] = function(k) return function(s, o, pc) -- JCN
    local p = s[256]
    local t, n = s[p], s[band(p - 1, 255)]
    s[256] = band(p + 2 * k - 2, 255)
    if n ~= 0 then pc = band(pc + signed(t), 65535) end
    return pc
  end end
  ops[0x2d] = function(k) return function(s, o, pc) -- JCN2
    local p = s[256]
    local t = bor(lshift(s[band(p - 1, 255)], 8), s[p])
    local n = s[band(p - 2, 255)]
    s[256] = band(p + 3 * k - 3, 255)
    if n ~= 0 then pc = t end
    return pc
  end end
  ops[0x0e] = function(k) return function(s, o, pc) -- JSR
    local p = s[256]
    local t = s[p]
    s[256] = band(p + k - 1, 255)
    local q = band(o[256] + 2, 255)
    put2(o, q, pc)
    o[256] = q
    pc = band(pc + signed(t), 65535)
    return pc
  end end
  ops[0x2e] = function(k) return function(s, o, pc) -- JSR2
    local p = s[256]
    local t = bor(lshift(s[band(p - 1, 255)], 8), s[p])
    s[256] = band(p + 2 * k - 2, 255)
    local q = band(o[256] + 2, 255)
    put2(o, q, pc)
    o[256] = q
    pc = t
    return pc
  end end
  ops[0x0f] = function(k) return function(s, o, pc) -- STH
    local p = s[256]
    local t = s[p]
    s[256] = band(p + k - 1, 255)
    local q = band(o[256] + 1, 255)
    o[q] = t
    o[256] = q
    return pc
  end end
  ops[0x2f] = function(k) return function(s, o, pc) -- STH2
    local p = s[256]
    local t1, t0 = s[band(p - 1, 255)], s[p]
    s[256] = band(p + 2 * k - 2, 255)
    local q = band(o[256] + 2, 255)
    o[band(q - 1, 255)], o[q] = t1, t0
    o[256] = q
    return pc
  end end

  ops[0x10] = function(k) return function(s, o, pc) -- LDZ
    local p = s[256]
    local t = s[p]
    p = band(p + k, 255)
    s[p] = ram[t]
    s[256] = p
    return pc
  end end
  ops[0x30] = function(k) return function(s, o, pc) -- LDZ2
    local p = s[256]
    local t = s[p]
    p = band(p + k + 1, 255)
    s[band(p - 1, 255)], s[p] = ram[t], ram[band(t + 1, 255)]
    s[256] = p
    return pc
  end end
  ops[0x11] = function(k) return function(s, o, pc) -- STZ
    local p = s[256]
    local t, n = s[p], s[band(p - 1, 255)]
    s[256] = band(p + 2 * k - 2, 255)
    ram[t] = n
    return pc
  end end
  ops[0x31] = function(k) return function(s, o, pc) -- STZ2
    local p = s[256]
    local t, n0, n1 = s[p], s[band(p - 1, 255)], s[band(p - 2, 255)]
    s[256] = band(p + 3 * k - 3, 255)
    ram[t], ram[band(t + 1, 255)] = n1, n0
    return pc
  end end
  ops[0x12] = function(k) return function(s, o, pc) -- LDR
    local p = s[256]
    local t = s[p]
    p = band(p + k, 255)
    s[p] = ram[band(pc + signed(t), 65535)]
    s[256] = p
    return pc
  end end
  ops[0x32] = function(k) return function(s, o, pc) -- LDR2
    local p = s[256]
    local r = band(pc + signed(s[p]), 65535)
    p = band(p + k + 1, 255)
    s[band(p - 1, 255)], s[p] = ram[r], ram[band(r + 1, 65535)]
    s[256] = p
    return pc
  end end
  ops[0x13] = function(k) return function(s, o, pc) -- STR
    local p = s[256]
    local t, n = s[p], s[band(p - 1, 255)]
    s[256] = band(p + 2 * k - 2, 255)
    ram[band(pc + signed(t), 65535)] = n
    return pc
  end end
  ops[0x33] = function(k) return function(s, o, pc) -- STR2
    local p = s[256]
    local t, n0, n1 = s[p], s[band(p - 1, 255)], s[band(p - 2, 255)]
    s[256] = band(p + 3 * k - 3, 255)
    local r = band(pc + signed(t), 65535)
    ram[r], ram[band(r + 1, 65535)] = n1, n0
    return pc
  end end
  ops[0x14] = function(k) return function(s, o, pc) -- LDA
    local p = s[256]
    local t = bor(lshift(s[band(p - 1, 255)], 8), s[p])
    p = band(p + 2 * k - 1, 255)
    s[p] = ram[t]
    s[256] = p
    return pc
  end end
  ops[0x34] = function(k) return function(s, o, pc) -- LDA2
    local p = s[256]
    local t = bor(lshift(s[band(p - 1, 255)], 8), s[p])
    p = band(p + 2 * k, 255)
    s[band(p - 1, 255)], s[p] = ram[t], ram[band(t + 1, 65535)]
    s[256] = p
    return pc
  end end
  ops[0x15] = function(k) return function(s, o, pc) -- STA
    local p = s[256]
    local t = bor(lshift(s[band(p - 1, 255)], 8), s[p])
    local n = s[band(p - 2, 255)]
    s[256] = band(p + 3 * k - 3, 255)
    ram[t] = n
    return pc
  end end
  ops[0x35] = function(k) return function(s, o, pc) -- STA2
    local p = s[256]
    local t = bor(lshift(s[band(p - 1, 255)], 8), s[p])
    local n1, n0 = s[band(p - 3, 255)], s[band(p - 2, 255)]
    s[256] = band(p + 4 * k - 4, 255)
    ram[t], ram[band(t + 1, 65535)] = n1, n0
    return pc
  end end
  ops[0x16] = function(k) return function(s, o, pc) -- DEI
    local p = s[256]
    local t = s[p]
    p = band(p + k, 255)
    s[256] = p
    s[p] = dei(t)
    return pc
  end end
  ops[0x36] = function(k) return function(s, o, pc) -- DEI2
    local p = s[256]
    local t = s[p]
    p = band(p + k + 1, 255)
    s[256] = p
    s[band(p - 1, 255)] = dei(t)
    s[p] = dei(band(t + 1, 255))
    return pc
  end end
  ops[0x17] = function(k) return function(s, o, pc) -- DEO
    local p = s[256]
    local t, n = s[p], s[band(p - 1, 255)]
    s[256] = band(p + 2 * k - 2, 255)
    deo(t, n)
    return pc
  end end
  ops[0x37] = function(k) return function(s, o, pc) -- DEO2
    local p = s[256]
    local t, n, l = s[p], s[band(p - 1, 255)], s[band(p - 2, 255)]
    s[256] = band(p + 3 * k - 3, 255)
    deo(t, l)
    deo(band(t + 1, 255), n)
    return pc
  end end

  -- The arithmetic and bitwise operations: a byte from the top two, or a short
  -- from the top two shorts.
  local function arith(byte, short)
    return function(k) return function(s, o, pc)
      local p = s[256]
      local t, n = s[p], s[band(p - 1, 255)]
      p = band(p + 2 * k - 1, 255)
      s[p] = byte(n, t)
      s[256] = p
      return pc
    end end,
    function(k) return function(s, o, pc)
      local p = s[256]
      local t = bor(lshift(s[band(p - 1, 255)], 8), s[p])
      local n = bor(lshift(s[band(p - 3, 255)], 8), s[band(p - 2, 255)])
      p = band(p + 4 * k - 2, 255)
      put2(s, p, short(n, t))
      s[256] = p
      return pc
    end end
  end
  ops[0x18], ops[0x38] = arith( -- ADD
    function(n, t) return band(n + t, 255) end,
    function(n, t) return band(n + t, 65535) end)
  ops[0x19], ops[0x39] = arith( -- SUB
    function(n, t) return band(n - t, 255) end,
    function(n, t) return band(n - t, 65535) end)
  ops[0x1a], ops[0x3a] = arith( -- MUL
    function(n, t) return band(n * t, 255) end,
    function(n, t) return band(n * t, 65535) end)
  local function div(n, t)
    if t == 0 then return 0 end
    return floor(n / t)
  end
  ops[0x1b], ops[0x3b] = arith(div, div) -- DIV
  ops[0x1c], ops[0x3c] = arith(band, band) -- AND
  ops[0x1d], ops[0x3d] = arith(bor, bor) -- ORA
  ops[0x1e], ops[0x3e] = arith(bxor, bxor) -- EOR
  ops[0x1f] = function(k) return function(s, o, pc) -- SFT
    local p = s[256]
    local t, n = s[p], s[band(p - 1, 255)]
    p = band(p + 2 * k - 1, 255)
    s[p] = band(lshift(rshift(n, band(t, 15)), rshift(t, 4)), 255)
    s[256] = p
    return pc
  end end
  ops[0x3f] = function(k) return function(s, o, pc) -- SFT2
    local p = s[256]
    local t = s[p]
    local n = bor(lshift(s[band(p - 2, 255)], 8), s[band(p - 1, 255)])
    p = band(p + 3 * k - 1, 255)
    put2(s, p, band(lshift(rshift(n, band(t, 15)), rshift(t, 4)), 65535))
    s[256] = p
    return pc
  end end

  -- The immediate operations, which have no keep flag: its bit picks LIT.
  local imm = {}
  imm[0x00] = function() end -- BRK
  imm[0x20] = function(s, o, pc) -- JCI
    local p = s[256]
    local t = s[p]
    s[256] = band(p - 1, 255)
    if t == 0 then
      pc = band(pc + 2, 65535)
    else
      pc = band(pc + 2 + bor(lshift(ram[pc], 8), ram[band(pc + 1, 65535)]), 65535)
    end
    return pc
  end
  imm[0x40] = function(s, o, pc) -- JMI
    pc = band(pc + 2 + bor(lshift(ram[pc], 8), ram[band(pc + 1, 65535)]), 65535)
    return pc
  end
  imm[0x60] = function(s, o, pc) -- JSI
    local q = band(s[256] + 2, 255)
    local rel = bor(lshift(ram[pc], 8), ram[band(pc + 1, 65535)])
    pc = band(pc + 2, 65535)
    put2(s, q, pc)
    s[256] = q
    pc = band(pc + rel, 65535)
    return pc
  end
  local function lit(s, o, pc)
    local q = band(s[256] + 1, 255)
    s[q] = ram[pc]
    s[256] = q
    pc = band(pc + 1, 65535)
    return pc
  end
  local function lit2(s, o, pc)
    local q = band(s[256] + 2, 255)
    s[band(q - 1, 255)], s[q] = ram[pc], ram[band(pc + 1, 65535)]
    s[256] = q
    pc = band(pc + 2, 65535)
    return pc
  end
  imm[0x80], imm[0xc0], imm[0xa0], imm[0xe0] = lit, lit, lit2, lit2

  -- Each instruction's operation, and whether it works on the return stack.
  local op, ret = {}, {}
  for ins = 0, 255 do
    if band(ins, 0x1f) == 0 then
      op[ins] = imm[ins]
    else
      op[ins] = ops[band(ins, 0x3f)](rshift(ins, 7))
    end
    ret[ins] = band(ins, 0x40) ~= 0
  end

  local vm = { ram = ram, wst = wst, rst = rst }

  function vm.set_devices(read, write)
    dei, deo = read, write
  end

  -- Run from `addr` until BRK. Where the Lua has `jit.promote` (lunacy), the
  -- program counter and the instruction there are promoted, so the loop is
  -- compiled once per guest instruction, its operation's call to one function.
  if promote then
    function vm.eval(addr)
      local pc = addr
      repeat
        pc = promote(pc)
        local ins = promote(ram[pc])
        pc = band(pc + 1, 65535)
        if ret[ins] then pc = op[ins](rst, wst, pc) else pc = op[ins](wst, rst, pc) end
      until not pc
    end
  else
    function vm.eval(addr)
      local pc = addr
      repeat
        local ins = ram[pc]
        pc = band(pc + 1, 65535)
        if ret[ins] then pc = op[ins](rst, wst, pc) else pc = op[ins](wst, rst, pc) end
      until not pc
    end
  end

  -- Load a ROM, a string, at the program's start, 0x100.
  function vm.load(rom)
    if #rom > 65536 - 256 then error("uxn: a ROM past 64KB needs expansion memory") end
    for i = 1, #rom do ram[255 + i] = rom:byte(i) end
  end

  return vm
end

return M
