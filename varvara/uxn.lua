-- The Uxn CPU (https://wiki.xxiivv.com/site/uxn.html), as the reference
-- implementation (uxn.c) runs it: 64KB of RAM, and two 256-byte circular
-- stacks, the working stack and the return stack.
--
-- Written in the subset of Lua 5.1 that LuaJIT, Lua 5.5 and Luau share, and
-- with no bit library: bitwise operations on bytes are table lookups, and on
-- shorts two of them.
--
-- Tables are indexed from 1, as Lua's arrays are: what is at address or
-- position `x` is at `x + 1`.
--
-- A stack is a table: its bytes at positions 0..255, and its pointer, the
-- position of its top byte, at 257. An instruction reads its operands below the pointer, moves
-- it, and writes its results below the new pointer; with the keep flag the
-- pointer moves past the operands instead, leaving them. So each operation is
-- its pointer's move with and without keep, as the reference's table of them
-- has it (`move`'s arguments below are the reference's `SET(x, y)`).

local floor = math.floor

local M = {}

-- lunacy's `jit.promote`, where the Lua has it. See `eval`.
local promote = jit and jit.promote
-- lunacy's `jit.learn`: what the specializer can know of a table's fields, learned once.
local learn = jit and jit.learn

-- AND, OR and XOR of two bytes, at a * 256 + b + 1.
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
      nibble_and[a * 16 + b + 1], nibble_or[a * 16 + b + 1], nibble_xor[a * 16 + b + 1] = r_and, r_or, r_xor
    end
  end
  for a = 0, 255 do
    local ah, al = floor(a / 16), a % 16
    for b = 0, 255 do
      local hi, lo = ah * 16 + floor(b / 16), al * 16 + b % 16
      local i = a * 256 + b
      AND[i + 1] = nibble_and[hi + 1] * 16 + nibble_and[lo + 1]
      ORA[i + 1] = nibble_or[hi + 1] * 16 + nibble_or[lo + 1]
      EOR[i + 1] = nibble_xor[hi + 1] * 16 + nibble_xor[lo + 1]
    end
  end
end

-- 2^n, for shifts, by multiplying: `^` makes a float in Lua 5.3 and later.
local POW2 = { 1 }
for n = 1, 15 do POW2[n + 1] = POW2[n] * 2 end

-- A machine is a table of its state: its RAM, `ram`, its stacks, `wst` and
-- `rst`, the device hooks `dei` and `deo`, and the tables its operations read,
-- each a field. Its operations are shared by every machine: each is given the
-- machine, its stack `s`, the other stack `o` for the operations moving a value
-- onto it, the program counter `pc` past its instruction, and its keep flag `k`
-- (0 or 1), and reads the machine's state from its fields, so it captures
-- nothing. It returns the program counter to go on from, or nothing to stop the
-- machine. The program counter is a local of `eval`, threaded through the
-- operations.

local ops = {}

ops[0x01] = function(m, s, o, pc, k) -- INC
  local p = s[257]
  local t = s[p + 1]
  p = (p + k) % 256
  s[p + 1] = (t + 1) % 256
  s[257] = p
  return pc
end
ops[0x21] = function(m, s, o, pc, k) -- INC2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  p = (p + 2 * k) % 256
  local v = (t + 1) % 65536
  s[p + 1] = v % 256
  s[(p - 1) % 256 + 1] = floor(v / 256) % 256
  s[257] = p
  return pc
end
ops[0x02] = function(m, s, o, pc, k) -- POP
  s[257] = (s[257] + k - 1) % 256
  return pc
end
ops[0x22] = function(m, s, o, pc, k) -- POP2
  s[257] = (s[257] + 2 * k - 2) % 256
  return pc
end
ops[0x03] = function(m, s, o, pc, k) -- NIP
  local p = s[257]
  local t = s[p + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = t
  s[257] = p
  return pc
end
ops[0x23] = function(m, s, o, pc, k) -- NIP2
  local p = s[257]
  local t, tl = s[(p - 1) % 256 + 1], s[p + 1]
  p = (p + 4 * k - 2) % 256
  s[p + 1], s[(p - 1) % 256 + 1] = tl, t
  s[257] = p
  return pc
end
ops[0x04] = function(m, s, o, pc, k) -- SWP
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k) % 256
  s[p + 1], s[(p - 1) % 256 + 1] = n, t
  s[257] = p
  return pc
end
ops[0x24] = function(m, s, o, pc, k) -- SWP2
  local p = s[257]
  local t1, t0, n1, n0 = s[(p - 1) % 256 + 1], s[p + 1], s[(p - 3) % 256 + 1], s[(p - 2) % 256 + 1]
  p = (p + 4 * k) % 256
  s[(p - 1) % 256 + 1], s[p + 1], s[(p - 3) % 256 + 1], s[(p - 2) % 256 + 1] = n1, n0, t1, t0
  s[257] = p
  return pc
end
ops[0x05] = function(m, s, o, pc, k) -- ROT
  local p = s[257]
  local t, n, l = s[p + 1], s[(p - 1) % 256 + 1], s[(p - 2) % 256 + 1]
  p = (p + 3 * k) % 256
  s[p + 1], s[(p - 1) % 256 + 1], s[(p - 2) % 256 + 1] = l, t, n
  s[257] = p
  return pc
end
ops[0x25] = function(m, s, o, pc, k) -- ROT2
  local p = s[257]
  local t1, t0 = s[(p - 1) % 256 + 1], s[p + 1]
  local n1, n0 = s[(p - 3) % 256 + 1], s[(p - 2) % 256 + 1]
  local l1, l0 = s[(p - 5) % 256 + 1], s[(p - 4) % 256 + 1]
  p = (p + 6 * k) % 256
  s[(p - 1) % 256 + 1], s[p + 1] = l1, l0
  s[(p - 3) % 256 + 1], s[(p - 2) % 256 + 1] = t1, t0
  s[(p - 5) % 256 + 1], s[(p - 4) % 256 + 1] = n1, n0
  s[257] = p
  return pc
end
ops[0x06] = function(m, s, o, pc, k) -- DUP
  local p = s[257]
  local t = s[p + 1]
  p = (p + k + 1) % 256
  s[p + 1], s[(p - 1) % 256 + 1] = t, t
  s[257] = p
  return pc
end
ops[0x26] = function(m, s, o, pc, k) -- DUP2
  local p = s[257]
  local t1, t0 = s[(p - 1) % 256 + 1], s[p + 1]
  p = (p + 2 * k + 2) % 256
  s[(p - 1) % 256 + 1], s[p + 1] = t1, t0
  s[(p - 3) % 256 + 1], s[(p - 2) % 256 + 1] = t1, t0
  s[257] = p
  return pc
end
ops[0x07] = function(m, s, o, pc, k) -- OVR
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k + 1) % 256
  s[p + 1], s[(p - 1) % 256 + 1], s[(p - 2) % 256 + 1] = n, t, n
  s[257] = p
  return pc
end
ops[0x27] = function(m, s, o, pc, k) -- OVR2
  local p = s[257]
  local t1, t0, n1, n0 = s[(p - 1) % 256 + 1], s[p + 1], s[(p - 3) % 256 + 1], s[(p - 2) % 256 + 1]
  p = (p + 4 * k + 2) % 256
  s[(p - 1) % 256 + 1], s[p + 1] = n1, n0
  s[(p - 3) % 256 + 1], s[(p - 2) % 256 + 1] = t1, t0
  s[(p - 5) % 256 + 1], s[(p - 4) % 256 + 1] = n1, n0
  s[257] = p
  return pc
end


-- The comparisons: a byte flag from the top two bytes, or shorts.
ops[0x08] = function(m, s, o, pc, k) -- EQU
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = n == t and 1 or 0
  s[257] = p
  return pc
end
ops[0x28] = function(m, s, o, pc, k) -- EQU2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 3) % 256 + 1] * 256 + s[(p - 2) % 256 + 1]
  p = (p + 4 * k - 3) % 256
  s[p + 1] = n == t and 1 or 0
  s[257] = p
  return pc
end
ops[0x09] = function(m, s, o, pc, k) -- NEQ
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = n ~= t and 1 or 0
  s[257] = p
  return pc
end
ops[0x29] = function(m, s, o, pc, k) -- NEQ2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 3) % 256 + 1] * 256 + s[(p - 2) % 256 + 1]
  p = (p + 4 * k - 3) % 256
  s[p + 1] = n ~= t and 1 or 0
  s[257] = p
  return pc
end
ops[0x0a] = function(m, s, o, pc, k) -- GTH
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = n > t and 1 or 0
  s[257] = p
  return pc
end
ops[0x2a] = function(m, s, o, pc, k) -- GTH2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 3) % 256 + 1] * 256 + s[(p - 2) % 256 + 1]
  p = (p + 4 * k - 3) % 256
  s[p + 1] = n > t and 1 or 0
  s[257] = p
  return pc
end
ops[0x0b] = function(m, s, o, pc, k) -- LTH
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = n < t and 1 or 0
  s[257] = p
  return pc
end
ops[0x2b] = function(m, s, o, pc, k) -- LTH2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 3) % 256 + 1] * 256 + s[(p - 2) % 256 + 1]
  p = (p + 4 * k - 3) % 256
  s[p + 1] = n < t and 1 or 0
  s[257] = p
  return pc
end

ops[0x0c] = function(m, s, o, pc, k) -- JMP
  local p = s[257]
  local t = s[p + 1]
  s[257] = (p + k - 1) % 256
  pc = (pc + (t + 128) % 256 - 128) % 65536
  return pc
end
ops[0x2c] = function(m, s, o, pc, k) -- JMP2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  s[257] = (p + 2 * k - 2) % 256
  pc = t
  return pc
end
ops[0x0d] = function(m, s, o, pc, k) -- JCN
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  s[257] = (p + 2 * k - 2) % 256
  if n ~= 0 then pc = (pc + (t + 128) % 256 - 128) % 65536 end
  return pc
end
ops[0x2d] = function(m, s, o, pc, k) -- JCN2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 2) % 256 + 1]
  s[257] = (p + 3 * k - 3) % 256
  if n ~= 0 then pc = t end
  return pc
end
ops[0x0e] = function(m, s, o, pc, k) -- JSR
  local p = s[257]
  local t = s[p + 1]
  s[257] = (p + k - 1) % 256
  local q = (o[257] + 2) % 256
  local v = pc
  o[q + 1] = v % 256
  o[(q - 1) % 256 + 1] = floor(v / 256) % 256
  o[257] = q
  pc = (pc + (t + 128) % 256 - 128) % 65536
  return pc
end
ops[0x2e] = function(m, s, o, pc, k) -- JSR2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  s[257] = (p + 2 * k - 2) % 256
  local q = (o[257] + 2) % 256
  local v = pc
  o[q + 1] = v % 256
  o[(q - 1) % 256 + 1] = floor(v / 256) % 256
  o[257] = q
  pc = t
  return pc
end
ops[0x0f] = function(m, s, o, pc, k) -- STH
  local p = s[257]
  local t = s[p + 1]
  s[257] = (p + k - 1) % 256
  local q = (o[257] + 1) % 256
  o[q + 1] = t
  o[257] = q
  return pc
end
ops[0x2f] = function(m, s, o, pc, k) -- STH2
  local p = s[257]
  local t1, t0 = s[(p - 1) % 256 + 1], s[p + 1]
  s[257] = (p + 2 * k - 2) % 256
  local q = (o[257] + 2) % 256
  o[(q - 1) % 256 + 1], o[q + 1] = t1, t0
  o[257] = q
  return pc
end

ops[0x10] = function(m, s, o, pc, k) -- LDZ
  local ram = m.ram
  local p = s[257]
  local t = s[p + 1]
  p = (p + k) % 256
  s[p + 1] = ram[t + 1]
  s[257] = p
  return pc
end
ops[0x30] = function(m, s, o, pc, k) -- LDZ2
  local ram = m.ram
  local p = s[257]
  local t = s[p + 1]
  p = (p + k + 1) % 256
  s[(p - 1) % 256 + 1], s[p + 1] = ram[t + 1], ram[(t + 1) % 256 + 1]
  s[257] = p
  return pc
end
ops[0x11] = function(m, s, o, pc, k) -- STZ
  local ram = m.ram
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  s[257] = (p + 2 * k - 2) % 256
  ram[t + 1] = n
  return pc
end
ops[0x31] = function(m, s, o, pc, k) -- STZ2
  local ram = m.ram
  local p = s[257]
  local t, n0, n1 = s[p + 1], s[(p - 1) % 256 + 1], s[(p - 2) % 256 + 1]
  s[257] = (p + 3 * k - 3) % 256
  ram[t + 1], ram[(t + 1) % 256 + 1] = n1, n0
  return pc
end
ops[0x12] = function(m, s, o, pc, k) -- LDR
  local ram = m.ram
  local p = s[257]
  local t = s[p + 1]
  p = (p + k) % 256
  s[p + 1] = ram[(pc + (t + 128) % 256 - 128) % 65536 + 1]
  s[257] = p
  return pc
end
ops[0x32] = function(m, s, o, pc, k) -- LDR2
  local ram = m.ram
  local p = s[257]
  local r = (pc + (s[p + 1] + 128) % 256 - 128) % 65536
  p = (p + k + 1) % 256
  s[(p - 1) % 256 + 1], s[p + 1] = ram[r + 1], ram[(r + 1) % 65536 + 1]
  s[257] = p
  return pc
end
ops[0x13] = function(m, s, o, pc, k) -- STR
  local ram = m.ram
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  s[257] = (p + 2 * k - 2) % 256
  ram[(pc + (t + 128) % 256 - 128) % 65536 + 1] = n
  return pc
end
ops[0x33] = function(m, s, o, pc, k) -- STR2
  local ram = m.ram
  local p = s[257]
  local t, n0, n1 = s[p + 1], s[(p - 1) % 256 + 1], s[(p - 2) % 256 + 1]
  s[257] = (p + 3 * k - 3) % 256
  local r = (pc + (t + 128) % 256 - 128) % 65536
  ram[r + 1], ram[(r + 1) % 65536 + 1] = n1, n0
  return pc
end
ops[0x14] = function(m, s, o, pc, k) -- LDA
  local ram = m.ram
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = ram[t + 1]
  s[257] = p
  return pc
end
ops[0x34] = function(m, s, o, pc, k) -- LDA2
  local ram = m.ram
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  p = (p + 2 * k) % 256
  s[(p - 1) % 256 + 1], s[p + 1] = ram[t + 1], ram[(t + 1) % 65536 + 1]
  s[257] = p
  return pc
end
ops[0x15] = function(m, s, o, pc, k) -- STA
  local ram = m.ram
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 2) % 256 + 1]
  s[257] = (p + 3 * k - 3) % 256
  ram[t + 1] = n
  return pc
end
ops[0x35] = function(m, s, o, pc, k) -- STA2
  local ram = m.ram
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n1, n0 = s[(p - 3) % 256 + 1], s[(p - 2) % 256 + 1]
  s[257] = (p + 4 * k - 4) % 256
  ram[t + 1], ram[(t + 1) % 65536 + 1] = n1, n0
  return pc
end
ops[0x16] = function(m, s, o, pc, k) -- DEI
  local dei = m.dei
  local p = s[257]
  local t = s[p + 1]
  p = (p + k) % 256
  s[257] = p
  s[p + 1] = dei(t)
  return pc
end
ops[0x36] = function(m, s, o, pc, k) -- DEI2
  local dei = m.dei
  local p = s[257]
  local t = s[p + 1]
  p = (p + k + 1) % 256
  s[257] = p
  s[(p - 1) % 256 + 1] = dei(t)
  s[p + 1] = dei((t + 1) % 256)
  return pc
end
ops[0x17] = function(m, s, o, pc, k) -- DEO
  local deo = m.deo
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  s[257] = (p + 2 * k - 2) % 256
  deo(t, n)
  return pc
end
ops[0x37] = function(m, s, o, pc, k) -- DEO2
  local deo = m.deo
  local p = s[257]
  local t, n, l = s[p + 1], s[(p - 1) % 256 + 1], s[(p - 2) % 256 + 1]
  s[257] = (p + 3 * k - 3) % 256
  deo(t, l)
  deo((t + 1) % 256, n)
  return pc
end

-- The arithmetic and bitwise operations: a byte from the top two, or a short
-- from the top two shorts.
ops[0x18] = function(m, s, o, pc, k) -- ADD
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = (n + t) % 256
  s[257] = p
  return pc
end
ops[0x38] = function(m, s, o, pc, k) -- ADD2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 3) % 256 + 1] * 256 + s[(p - 2) % 256 + 1]
  p = (p + 4 * k - 2) % 256
  local v = (n + t) % 65536
  s[p + 1] = v % 256
  s[(p - 1) % 256 + 1] = floor(v / 256) % 256
  s[257] = p
  return pc
end
ops[0x19] = function(m, s, o, pc, k) -- SUB
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = (n - t) % 256
  s[257] = p
  return pc
end
ops[0x39] = function(m, s, o, pc, k) -- SUB2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 3) % 256 + 1] * 256 + s[(p - 2) % 256 + 1]
  p = (p + 4 * k - 2) % 256
  local v = (n - t) % 65536
  s[p + 1] = v % 256
  s[(p - 1) % 256 + 1] = floor(v / 256) % 256
  s[257] = p
  return pc
end
ops[0x1a] = function(m, s, o, pc, k) -- MUL
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = (n * t) % 256
  s[257] = p
  return pc
end
ops[0x3a] = function(m, s, o, pc, k) -- MUL2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 3) % 256 + 1] * 256 + s[(p - 2) % 256 + 1]
  p = (p + 4 * k - 2) % 256
  local v = (n * t) % 65536
  s[p + 1] = v % 256
  s[(p - 1) % 256 + 1] = floor(v / 256) % 256
  s[257] = p
  return pc
end
ops[0x1b] = function(m, s, o, pc, k) -- DIV
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = t == 0 and 0 or floor(n / t)
  s[257] = p
  return pc
end
ops[0x3b] = function(m, s, o, pc, k) -- DIV2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 3) % 256 + 1] * 256 + s[(p - 2) % 256 + 1]
  p = (p + 4 * k - 2) % 256
  local v = t == 0 and 0 or floor(n / t)
  s[p + 1] = v % 256
  s[(p - 1) % 256 + 1] = floor(v / 256) % 256
  s[257] = p
  return pc
end
ops[0x1c] = function(m, s, o, pc, k) -- AND
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = m.AND[n * 256 + t + 1]
  s[257] = p
  return pc
end
ops[0x3c] = function(m, s, o, pc, k) -- AND2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 3) % 256 + 1] * 256 + s[(p - 2) % 256 + 1]
  p = (p + 4 * k - 2) % 256
  local v = m.AND[floor(n / 256) * 256 + floor(t / 256) + 1] * 256 + m.AND[(n % 256) * 256 + t % 256 + 1]
  s[p + 1] = v % 256
  s[(p - 1) % 256 + 1] = floor(v / 256) % 256
  s[257] = p
  return pc
end
ops[0x1d] = function(m, s, o, pc, k) -- ORA
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = m.ORA[n * 256 + t + 1]
  s[257] = p
  return pc
end
ops[0x3d] = function(m, s, o, pc, k) -- ORA2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 3) % 256 + 1] * 256 + s[(p - 2) % 256 + 1]
  p = (p + 4 * k - 2) % 256
  local v = m.ORA[floor(n / 256) * 256 + floor(t / 256) + 1] * 256 + m.ORA[(n % 256) * 256 + t % 256 + 1]
  s[p + 1] = v % 256
  s[(p - 1) % 256 + 1] = floor(v / 256) % 256
  s[257] = p
  return pc
end
ops[0x1e] = function(m, s, o, pc, k) -- EOR
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = m.EOR[n * 256 + t + 1]
  s[257] = p
  return pc
end
ops[0x3e] = function(m, s, o, pc, k) -- EOR2
  local p = s[257]
  local t = s[(p - 1) % 256 + 1] * 256 + s[p + 1]
  local n = s[(p - 3) % 256 + 1] * 256 + s[(p - 2) % 256 + 1]
  p = (p + 4 * k - 2) % 256
  local v = m.EOR[floor(n / 256) * 256 + floor(t / 256) + 1] * 256 + m.EOR[(n % 256) * 256 + t % 256 + 1]
  s[p + 1] = v % 256
  s[(p - 1) % 256 + 1] = floor(v / 256) % 256
  s[257] = p
  return pc
end

ops[0x1f] = function(m, s, o, pc, k) -- SFT
  local POW2 = m.POW2
  local p = s[257]
  local t, n = s[p + 1], s[(p - 1) % 256 + 1]
  p = (p + 2 * k - 1) % 256
  s[p + 1] = floor(n / POW2[t % 16 + 1]) * POW2[floor(t / 16) + 1] % 256
  s[257] = p
  return pc
end
ops[0x3f] = function(m, s, o, pc, k) -- SFT2
  local POW2 = m.POW2
  local p = s[257]
  local t = s[p + 1]
  local n = s[(p - 2) % 256 + 1] * 256 + s[(p - 1) % 256 + 1]
  p = (p + 3 * k - 1) % 256
  local v = floor(n / POW2[t % 16 + 1]) * POW2[floor(t / 16) + 1] % 65536
  s[p + 1] = v % 256
  s[(p - 1) % 256 + 1] = floor(v / 256) % 256
  s[257] = p
  return pc
end

-- The immediate operations, which have no keep flag: its bit picks LIT.
local imm = {}
imm[0x00] = function() end -- BRK
imm[0x20] = function(m, s, o, pc, k) -- JCI
  local ram = m.ram
  local p = s[257]
  local t = s[p + 1]
  s[257] = (p - 1) % 256
  if t == 0 then
    pc = (pc + 2) % 65536
  else
    pc = (pc + 2 + ram[pc + 1] * 256 + ram[(pc + 1) % 65536 + 1]) % 65536
  end
  return pc
end
imm[0x40] = function(m, s, o, pc, k) -- JMI
  local ram = m.ram
  pc = (pc + 2 + ram[pc + 1] * 256 + ram[(pc + 1) % 65536 + 1]) % 65536
  return pc
end
imm[0x60] = function(m, s, o, pc, k) -- JSI
  local ram = m.ram
  local q = (s[257] + 2) % 256
  local rel = ram[pc + 1] * 256 + ram[(pc + 1) % 65536 + 1]
  pc = (pc + 2) % 65536
  local v = pc
  s[q + 1] = v % 256
  s[(q - 1) % 256 + 1] = floor(v / 256) % 256
  s[257] = q
  pc = (pc + rel) % 65536
  return pc
end
local function lit(m, s, o, pc, k)
  local ram = m.ram
  local q = (s[257] + 1) % 256
  s[q + 1] = ram[pc + 1]
  s[257] = q
  pc = (pc + 1) % 65536
  return pc
end
local function lit2(m, s, o, pc, k)
  local ram = m.ram
  local q = (s[257] + 2) % 256
  s[(q - 1) % 256 + 1], s[q + 1] = ram[pc + 1], ram[(pc + 1) % 65536 + 1]
  s[257] = q
  pc = (pc + 2) % 65536
  return pc
end
imm[0x80], imm[0xc0], imm[0xa0], imm[0xe0] = lit, lit, lit2, lit2


-- Each instruction's operation, its keep flag, and whether it works on the
-- return stack.
local OP, KEEP, RET = {}, {}, {}
for ins = 0, 255 do
  if ins % 32 == 0 then
    OP[ins + 1] = imm[ins]
  else
    OP[ins + 1] = ops[ins % 64]
  end
  KEEP[ins + 1] = floor(ins / 128)
  RET[ins + 1] = ins % 128 >= 64
end

-- The machine's methods, `m:eval(addr)` and so on, shared by every machine.

-- Run machine `m` from `addr` until BRK, its state read from its fields once a
-- run, `m` a local each operation is given. Where the Lua has `jit.promote`
-- (lunacy), the program counter and the instruction there are promoted, so the
-- loop is compiled once per guest instruction, its operation's call to one
-- function.
local eval
if promote then
  function eval(m, addr)
    learn(m)
    local ram, wst, rst, op, keep, ret = m.ram, m.wst, m.rst, m.op, m.keep, m.ret
    local pc = addr
    repeat
      pc = promote(pc)
      local ins = promote(ram[pc + 1])
      pc = (pc + 1) % 65536
      if ret[ins + 1] then pc = op[ins + 1](m, rst, wst, pc, keep[ins + 1]) else pc = op[ins + 1](m, wst, rst, pc, keep[ins + 1]) end
    until not pc
  end
else
  function eval(m, addr)
    local ram, wst, rst, op, keep, ret = m.ram, m.wst, m.rst, m.op, m.keep, m.ret
    local pc = addr
    repeat
      local ins = ram[pc + 1]
      pc = (pc + 1) % 65536
      if ret[ins + 1] then pc = op[ins + 1](m, rst, wst, pc, keep[ins + 1]) else pc = op[ins + 1](m, wst, rst, pc, keep[ins + 1]) end
    until not pc
  end
end

-- Set the device hooks: `read(port)` reads a device port, and `write(port,
-- value)` writes one.
local function set_devices(m, read, write)
  m.dei, m.deo = read, write
end

-- Load a ROM, a string, at the program's start, 0x100.
local function load(m, rom)
  if #rom > 65536 - 256 then error("uxn: a ROM past 64KB needs expansion memory") end
  local ram = m.ram
  for i = 1, #rom do ram[256 + i] = rom:byte(i) end
end

-- A new machine with zeroed memory. `dei(port)` reads a device port, and
-- `deo(port, value)` writes one, as `set_devices` sets them.
function M.new()
  local m = {
    ram = {}, wst = {}, rst = {},
    dei = function() return 0 end, deo = function() end,
    op = OP, keep = KEEP, ret = RET,
    eval = eval, load = load, set_devices = set_devices,
    AND = AND, ORA = ORA, EOR = EOR, POW2 = POW2,
  }
  local ram, wst, rst = m.ram, m.wst, m.rst
  for i = 1, 65536 do ram[i] = 0 end
  for i = 1, 257 do wst[i], rst[i] = 0, 0 end

  return m
end

return M
