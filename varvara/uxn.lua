-- The Uxn CPU (https://wiki.xxiivv.com/site/uxn.html), as the reference
-- implementation (uxn.c) runs it: 64KB of RAM, and two 256-byte circular
-- stacks, the working stack and the return stack.
--
-- Written in the subset of Lua 5.1 that LuaJIT, Lua 5.5 and Luau share, and
-- with no bit library: bitwise operations on bytes are table lookups, and on
-- shorts two of them.
--
-- A stack is a table: its bytes at 0..255, and its pointer, the index of its
-- top byte, at 256. An instruction reads its operands below the pointer, moves
-- it, and writes its results below the new pointer; with the keep flag the
-- pointer moves past the operands instead, leaving them. So each operation is
-- its pointer's move with and without keep, as the reference's table of them
-- has it (`move`'s arguments below are the reference's `SET(x, y)`).

local floor = math.floor

local M = {}

-- AND, OR and XOR of two bytes, at a * 256 + b.
local AND, ORA, EOR = {}, {}, {}
do
  local nibble_and, nibble_or, nibble_xor = {}, {}, {}
  for a = 0, 15 do
    for b = 0, 15 do
      local r_and, r_or, r_xor, bit = 0, 0, 0, 1
      local x, y = a, b
      for _ = 1, 4 do
        local xb, yb = x % 2, y % 2
        if xb == 1 and yb == 1 then r_and = r_and + bit end
        if xb == 1 or yb == 1 then r_or = r_or + bit end
        if xb ~= yb then r_xor = r_xor + bit end
        x, y, bit = (x - xb) / 2, (y - yb) / 2, bit * 2
      end
      nibble_and[a * 16 + b], nibble_or[a * 16 + b], nibble_xor[a * 16 + b] = r_and, r_or, r_xor
    end
  end
  for a = 0, 255 do
    local ah, al = floor(a / 16), a % 16
    for b = 0, 255 do
      local hi, lo = ah * 16 + floor(b / 16), al * 16 + b % 16
      local i = a * 256 + b
      AND[i] = nibble_and[hi] * 16 + nibble_and[lo]
      ORA[i] = nibble_or[hi] * 16 + nibble_or[lo]
      EOR[i] = nibble_xor[hi] * 16 + nibble_xor[lo]
    end
  end
end

-- 2^n, for shifts, by multiplying: `^` makes a float in Lua 5.3 and later.
local POW2 = { [0] = 1 }
for n = 1, 15 do POW2[n] = POW2[n - 1] * 2 end

local function signed(byte)
  if byte >= 128 then return byte - 256 end
  return byte
end

-- A byte bitwise operation's short form.
local function short_op(t, a, b)
  return t[floor(a / 256) * 256 + floor(b / 256)] * 256 + t[(a % 256) * 256 + b % 256]
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
    s[p] = v % 256
    s[(p - 1) % 256] = floor(v / 256) % 256
  end

  ops[0x01] = function(k) return function(s, o, pc) -- INC
    local p = s[256]
    local t = s[p]
    p = (p + k) % 256
    s[p] = (t + 1) % 256
    s[256] = p
    return pc
  end end
  ops[0x21] = function(k) return function(s, o, pc) -- INC2
    local p = s[256]
    local t = s[(p - 1) % 256] * 256 + s[p]
    p = (p + 2 * k) % 256
    put2(s, p, (t + 1) % 65536)
    s[256] = p
    return pc
  end end
  ops[0x02] = function(k) return function(s, o, pc) -- POP
    s[256] = (s[256] + k - 1) % 256
    return pc
  end end
  ops[0x22] = function(k) return function(s, o, pc) -- POP2
    s[256] = (s[256] + 2 * k - 2) % 256
    return pc
  end end
  ops[0x03] = function(k) return function(s, o, pc) -- NIP
    local p = s[256]
    local t = s[p]
    p = (p + 2 * k - 1) % 256
    s[p] = t
    s[256] = p
    return pc
  end end
  ops[0x23] = function(k) return function(s, o, pc) -- NIP2
    local p = s[256]
    local t, tl = s[(p - 1) % 256], s[p]
    p = (p + 4 * k - 2) % 256
    s[p], s[(p - 1) % 256] = tl, t
    s[256] = p
    return pc
  end end
  ops[0x04] = function(k) return function(s, o, pc) -- SWP
    local p = s[256]
    local t, n = s[p], s[(p - 1) % 256]
    p = (p + 2 * k) % 256
    s[p], s[(p - 1) % 256] = n, t
    s[256] = p
    return pc
  end end
  ops[0x24] = function(k) return function(s, o, pc) -- SWP2
    local p = s[256]
    local t1, t0, n1, n0 = s[(p - 1) % 256], s[p], s[(p - 3) % 256], s[(p - 2) % 256]
    p = (p + 4 * k) % 256
    s[(p - 1) % 256], s[p], s[(p - 3) % 256], s[(p - 2) % 256] = n1, n0, t1, t0
    s[256] = p
    return pc
  end end
  ops[0x05] = function(k) return function(s, o, pc) -- ROT
    local p = s[256]
    local t, n, l = s[p], s[(p - 1) % 256], s[(p - 2) % 256]
    p = (p + 3 * k) % 256
    s[p], s[(p - 1) % 256], s[(p - 2) % 256] = l, t, n
    s[256] = p
    return pc
  end end
  ops[0x25] = function(k) return function(s, o, pc) -- ROT2
    local p = s[256]
    local t1, t0 = s[(p - 1) % 256], s[p]
    local n1, n0 = s[(p - 3) % 256], s[(p - 2) % 256]
    local l1, l0 = s[(p - 5) % 256], s[(p - 4) % 256]
    p = (p + 6 * k) % 256
    s[(p - 1) % 256], s[p] = l1, l0
    s[(p - 3) % 256], s[(p - 2) % 256] = t1, t0
    s[(p - 5) % 256], s[(p - 4) % 256] = n1, n0
    s[256] = p
    return pc
  end end
  ops[0x06] = function(k) return function(s, o, pc) -- DUP
    local p = s[256]
    local t = s[p]
    p = (p + k + 1) % 256
    s[p], s[(p - 1) % 256] = t, t
    s[256] = p
    return pc
  end end
  ops[0x26] = function(k) return function(s, o, pc) -- DUP2
    local p = s[256]
    local t1, t0 = s[(p - 1) % 256], s[p]
    p = (p + 2 * k + 2) % 256
    s[(p - 1) % 256], s[p] = t1, t0
    s[(p - 3) % 256], s[(p - 2) % 256] = t1, t0
    s[256] = p
    return pc
  end end
  ops[0x07] = function(k) return function(s, o, pc) -- OVR
    local p = s[256]
    local t, n = s[p], s[(p - 1) % 256]
    p = (p + 2 * k + 1) % 256
    s[p], s[(p - 1) % 256], s[(p - 2) % 256] = n, t, n
    s[256] = p
    return pc
  end end
  ops[0x27] = function(k) return function(s, o, pc) -- OVR2
    local p = s[256]
    local t1, t0, n1, n0 = s[(p - 1) % 256], s[p], s[(p - 3) % 256], s[(p - 2) % 256]
    p = (p + 4 * k + 2) % 256
    s[(p - 1) % 256], s[p] = n1, n0
    s[(p - 3) % 256], s[(p - 2) % 256] = t1, t0
    s[(p - 5) % 256], s[(p - 4) % 256] = n1, n0
    s[256] = p
    return pc
  end end

  -- The comparisons: a byte flag from the top two bytes, or shorts.
  local function compare(test)
    return function(k) return function(s, o, pc)
      local p = s[256]
      local t, n = s[p], s[(p - 1) % 256]
      p = (p + 2 * k - 1) % 256
      s[p] = test(n, t) and 1 or 0
      s[256] = p
      return pc
    end end,
    function(k) return function(s, o, pc)
      local p = s[256]
      local t = s[(p - 1) % 256] * 256 + s[p]
      local n = s[(p - 3) % 256] * 256 + s[(p - 2) % 256]
      p = (p + 4 * k - 3) % 256
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
    s[256] = (p + k - 1) % 256
    pc = (pc + signed(t)) % 65536
    return pc
  end end
  ops[0x2c] = function(k) return function(s, o, pc) -- JMP2
    local p = s[256]
    local t = s[(p - 1) % 256] * 256 + s[p]
    s[256] = (p + 2 * k - 2) % 256
    pc = t
    return pc
  end end
  ops[0x0d] = function(k) return function(s, o, pc) -- JCN
    local p = s[256]
    local t, n = s[p], s[(p - 1) % 256]
    s[256] = (p + 2 * k - 2) % 256
    if n ~= 0 then pc = (pc + signed(t)) % 65536 end
    return pc
  end end
  ops[0x2d] = function(k) return function(s, o, pc) -- JCN2
    local p = s[256]
    local t = s[(p - 1) % 256] * 256 + s[p]
    local n = s[(p - 2) % 256]
    s[256] = (p + 3 * k - 3) % 256
    if n ~= 0 then pc = t end
    return pc
  end end
  ops[0x0e] = function(k) return function(s, o, pc) -- JSR
    local p = s[256]
    local t = s[p]
    s[256] = (p + k - 1) % 256
    local q = (o[256] + 2) % 256
    put2(o, q, pc)
    o[256] = q
    pc = (pc + signed(t)) % 65536
    return pc
  end end
  ops[0x2e] = function(k) return function(s, o, pc) -- JSR2
    local p = s[256]
    local t = s[(p - 1) % 256] * 256 + s[p]
    s[256] = (p + 2 * k - 2) % 256
    local q = (o[256] + 2) % 256
    put2(o, q, pc)
    o[256] = q
    pc = t
    return pc
  end end
  ops[0x0f] = function(k) return function(s, o, pc) -- STH
    local p = s[256]
    local t = s[p]
    s[256] = (p + k - 1) % 256
    local q = (o[256] + 1) % 256
    o[q] = t
    o[256] = q
    return pc
  end end
  ops[0x2f] = function(k) return function(s, o, pc) -- STH2
    local p = s[256]
    local t1, t0 = s[(p - 1) % 256], s[p]
    s[256] = (p + 2 * k - 2) % 256
    local q = (o[256] + 2) % 256
    o[(q - 1) % 256], o[q] = t1, t0
    o[256] = q
    return pc
  end end

  ops[0x10] = function(k) return function(s, o, pc) -- LDZ
    local p = s[256]
    local t = s[p]
    p = (p + k) % 256
    s[p] = ram[t]
    s[256] = p
    return pc
  end end
  ops[0x30] = function(k) return function(s, o, pc) -- LDZ2
    local p = s[256]
    local t = s[p]
    p = (p + k + 1) % 256
    s[(p - 1) % 256], s[p] = ram[t], ram[(t + 1) % 256]
    s[256] = p
    return pc
  end end
  ops[0x11] = function(k) return function(s, o, pc) -- STZ
    local p = s[256]
    local t, n = s[p], s[(p - 1) % 256]
    s[256] = (p + 2 * k - 2) % 256
    ram[t] = n
    return pc
  end end
  ops[0x31] = function(k) return function(s, o, pc) -- STZ2
    local p = s[256]
    local t, n0, n1 = s[p], s[(p - 1) % 256], s[(p - 2) % 256]
    s[256] = (p + 3 * k - 3) % 256
    ram[t], ram[(t + 1) % 256] = n1, n0
    return pc
  end end
  ops[0x12] = function(k) return function(s, o, pc) -- LDR
    local p = s[256]
    local t = s[p]
    p = (p + k) % 256
    s[p] = ram[(pc + signed(t)) % 65536]
    s[256] = p
    return pc
  end end
  ops[0x32] = function(k) return function(s, o, pc) -- LDR2
    local p = s[256]
    local r = (pc + signed(s[p])) % 65536
    p = (p + k + 1) % 256
    s[(p - 1) % 256], s[p] = ram[r], ram[(r + 1) % 65536]
    s[256] = p
    return pc
  end end
  ops[0x13] = function(k) return function(s, o, pc) -- STR
    local p = s[256]
    local t, n = s[p], s[(p - 1) % 256]
    s[256] = (p + 2 * k - 2) % 256
    ram[(pc + signed(t)) % 65536] = n
    return pc
  end end
  ops[0x33] = function(k) return function(s, o, pc) -- STR2
    local p = s[256]
    local t, n0, n1 = s[p], s[(p - 1) % 256], s[(p - 2) % 256]
    s[256] = (p + 3 * k - 3) % 256
    local r = (pc + signed(t)) % 65536
    ram[r], ram[(r + 1) % 65536] = n1, n0
    return pc
  end end
  ops[0x14] = function(k) return function(s, o, pc) -- LDA
    local p = s[256]
    local t = s[(p - 1) % 256] * 256 + s[p]
    p = (p + 2 * k - 1) % 256
    s[p] = ram[t]
    s[256] = p
    return pc
  end end
  ops[0x34] = function(k) return function(s, o, pc) -- LDA2
    local p = s[256]
    local t = s[(p - 1) % 256] * 256 + s[p]
    p = (p + 2 * k) % 256
    s[(p - 1) % 256], s[p] = ram[t], ram[(t + 1) % 65536]
    s[256] = p
    return pc
  end end
  ops[0x15] = function(k) return function(s, o, pc) -- STA
    local p = s[256]
    local t = s[(p - 1) % 256] * 256 + s[p]
    local n = s[(p - 2) % 256]
    s[256] = (p + 3 * k - 3) % 256
    ram[t] = n
    return pc
  end end
  ops[0x35] = function(k) return function(s, o, pc) -- STA2
    local p = s[256]
    local t = s[(p - 1) % 256] * 256 + s[p]
    local n1, n0 = s[(p - 3) % 256], s[(p - 2) % 256]
    s[256] = (p + 4 * k - 4) % 256
    ram[t], ram[(t + 1) % 65536] = n1, n0
    return pc
  end end
  ops[0x16] = function(k) return function(s, o, pc) -- DEI
    local p = s[256]
    local t = s[p]
    p = (p + k) % 256
    s[256] = p
    s[p] = dei(t)
    return pc
  end end
  ops[0x36] = function(k) return function(s, o, pc) -- DEI2
    local p = s[256]
    local t = s[p]
    p = (p + k + 1) % 256
    s[256] = p
    s[(p - 1) % 256] = dei(t)
    s[p] = dei((t + 1) % 256)
    return pc
  end end
  ops[0x17] = function(k) return function(s, o, pc) -- DEO
    local p = s[256]
    local t, n = s[p], s[(p - 1) % 256]
    s[256] = (p + 2 * k - 2) % 256
    deo(t, n)
    return pc
  end end
  ops[0x37] = function(k) return function(s, o, pc) -- DEO2
    local p = s[256]
    local t, n, l = s[p], s[(p - 1) % 256], s[(p - 2) % 256]
    s[256] = (p + 3 * k - 3) % 256
    deo(t, l)
    deo((t + 1) % 256, n)
    return pc
  end end

  -- The arithmetic and bitwise operations: a byte from the top two, or a short
  -- from the top two shorts.
  local function arith(byte, short)
    return function(k) return function(s, o, pc)
      local p = s[256]
      local t, n = s[p], s[(p - 1) % 256]
      p = (p + 2 * k - 1) % 256
      s[p] = byte(n, t)
      s[256] = p
      return pc
    end end,
    function(k) return function(s, o, pc)
      local p = s[256]
      local t = s[(p - 1) % 256] * 256 + s[p]
      local n = s[(p - 3) % 256] * 256 + s[(p - 2) % 256]
      p = (p + 4 * k - 2) % 256
      put2(s, p, short(n, t))
      s[256] = p
      return pc
    end end
  end
  ops[0x18], ops[0x38] = arith( -- ADD
    function(n, t) return (n + t) % 256 end,
    function(n, t) return (n + t) % 65536 end)
  ops[0x19], ops[0x39] = arith( -- SUB
    function(n, t) return (n - t) % 256 end,
    function(n, t) return (n - t) % 65536 end)
  ops[0x1a], ops[0x3a] = arith( -- MUL
    function(n, t) return (n * t) % 256 end,
    function(n, t) return (n * t) % 65536 end)
  local function div(n, t)
    if t == 0 then return 0 end
    return floor(n / t)
  end
  ops[0x1b], ops[0x3b] = arith(div, div) -- DIV
  ops[0x1c], ops[0x3c] = arith( -- AND
    function(n, t) return AND[n * 256 + t] end,
    function(n, t) return short_op(AND, n, t) end)
  ops[0x1d], ops[0x3d] = arith( -- ORA
    function(n, t) return ORA[n * 256 + t] end,
    function(n, t) return short_op(ORA, n, t) end)
  ops[0x1e], ops[0x3e] = arith( -- EOR
    function(n, t) return EOR[n * 256 + t] end,
    function(n, t) return short_op(EOR, n, t) end)
  ops[0x1f] = function(k) return function(s, o, pc) -- SFT
    local p = s[256]
    local t, n = s[p], s[(p - 1) % 256]
    p = (p + 2 * k - 1) % 256
    s[p] = floor(n / POW2[t % 16]) * POW2[floor(t / 16)] % 256
    s[256] = p
    return pc
  end end
  ops[0x3f] = function(k) return function(s, o, pc) -- SFT2
    local p = s[256]
    local t = s[p]
    local n = s[(p - 2) % 256] * 256 + s[(p - 1) % 256]
    p = (p + 3 * k - 1) % 256
    put2(s, p, floor(n / POW2[t % 16]) * POW2[floor(t / 16)] % 65536)
    s[256] = p
    return pc
  end end

  -- The immediate operations, which have no keep flag: its bit picks LIT.
  local imm = {}
  imm[0x00] = function() end -- BRK
  imm[0x20] = function(s, o, pc) -- JCI
    local p = s[256]
    local t = s[p]
    s[256] = (p - 1) % 256
    if t == 0 then
      pc = (pc + 2) % 65536
    else
      pc = (pc + 2 + ram[pc] * 256 + ram[(pc + 1) % 65536]) % 65536
    end
    return pc
  end
  imm[0x40] = function(s, o, pc) -- JMI
    pc = (pc + 2 + ram[pc] * 256 + ram[(pc + 1) % 65536]) % 65536
    return pc
  end
  imm[0x60] = function(s, o, pc) -- JSI
    local q = (s[256] + 2) % 256
    local rel = ram[pc] * 256 + ram[(pc + 1) % 65536]
    pc = (pc + 2) % 65536
    put2(s, q, pc)
    s[256] = q
    pc = (pc + rel) % 65536
    return pc
  end
  local function lit(s, o, pc)
    local q = (s[256] + 1) % 256
    s[q] = ram[pc]
    s[256] = q
    pc = (pc + 1) % 65536
    return pc
  end
  local function lit2(s, o, pc)
    local q = (s[256] + 2) % 256
    s[(q - 1) % 256], s[q] = ram[pc], ram[(pc + 1) % 65536]
    s[256] = q
    pc = (pc + 2) % 65536
    return pc
  end
  imm[0x80], imm[0xc0], imm[0xa0], imm[0xe0] = lit, lit, lit2, lit2

  -- Each instruction's operation, and whether it works on the return stack.
  local op, ret = {}, {}
  for ins = 0, 255 do
    if ins % 32 == 0 then
      op[ins] = imm[ins]
    else
      op[ins] = ops[ins % 64](floor(ins / 128))
    end
    ret[ins] = ins % 128 >= 64
  end

  local vm = { ram = ram, wst = wst, rst = rst }

  function vm.set_devices(read, write)
    dei, deo = read, write
  end

  -- Run from `addr` until BRK.
  function vm.eval(addr)
    local pc = addr
    repeat
      local ins = ram[pc]
      pc = (pc + 1) % 65536
      if ret[ins] then pc = op[ins](rst, wst, pc) else pc = op[ins](wst, rst, pc) end
    until not pc
  end

  -- Load a ROM, a string, at the program's start, 0x100.
  function vm.load(rom)
    if #rom > 65536 - 256 then error("uxn: a ROM past 64KB needs expansion memory") end
    for i = 1, #rom do ram[255 + i] = rom:byte(i) end
  end

  return vm
end

return M
