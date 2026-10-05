-- The library functions written in Lua: those a native can't be, as they keep
-- state between calls or call a function. Run before every program, in its
-- global environment. See Note [Library natives] in `library`.

local find, sub, len = string.find, string.sub, string.len
local native_gsub = string.gsub
local concat, unpack, type, tostring, error = table.concat, unpack, type, tostring, error

-- Lua 5.1's `string.gmatch`: each match of `p` in `s`, searched from where the
-- last one ended, or a byte past an empty one, as its captures, or the whole
-- match if it has none. A leading `^` isn't an anchor, as in 5.1's.
function string.gmatch(s, p)
  if type(s) == "number" then
    s = tostring(s)
  end
  if sub(p, 1, 1) == "^" then
    p = "%" .. p
  end
  local at = 1
  return function()
    if at > len(s) + 1 then
      return nil
    end
    local found = {find(s, p, at)}
    local first, last = found[1], found[2]
    if not first then
      at = len(s) + 2
      return nil
    end
    if last >= first then
      at = last + 1
    else
      at = first + 1
    end
    if found[3] == nil then
      return sub(s, first, last)
    end
    return unpack(found, 3)
  end
end

-- Lua 5.1's `string.gsub`, the native's but for a function replacement: called
-- with each match's captures (or the whole match), its result replaces the
-- match, kept if nil or false.
function string.gsub(s, p, repl, n)
  if type(repl) ~= "function" then
    return native_gsub(s, p, repl, n)
  end
  if type(s) == "number" then
    s = tostring(s)
  end
  local anchor = sub(p, 1, 1) == "^"
  -- Matched only where the search is, as the native's matches: anchored.
  local at = anchor and p or "^" .. p
  local max = n or len(s) + 1
  local out, count, src = {}, 0, 1
  while count < max do
    local found = {find(s, at, src)}
    local last
    if found[1] then
      count = count + 1
      local value
      if found[3] == nil then
        value = repl(sub(s, found[1], found[2]))
      else
        value = repl(unpack(found, 3))
      end
      if not value then
        value = sub(s, found[1], found[2])
      elseif type(value) ~= "string" and type(value) ~= "number" then
        error("invalid replacement value (a " .. type(value) .. ")", 0)
      end
      out[#out + 1] = value
      last = found[2]
    end
    if last and last >= src then
      src = last + 1
    elseif src <= len(s) then
      out[#out + 1] = sub(s, src, src)
      src = src + 1
    else
      break
    end
    if anchor then
      break
    end
  end
  out[#out + 1] = sub(s, src)
  return concat(out), count
end

-- Lua 5.1's `table.sort` (ltablib.c's `auxsort`): a quicksort on the median of
-- three, recursing into the smaller part and looping on the larger.
local function less(a, b)
  return a < b
end

local function auxsort(t, lo, up, lt)
  while lo < up do
    if lt(t[up], t[lo]) then
      t[lo], t[up] = t[up], t[lo]
    end
    if up - lo == 1 then
      break
    end
    local p = math.floor((lo + up) / 2)
    if lt(t[p], t[lo]) then
      t[p], t[lo] = t[lo], t[p]
    elseif lt(t[up], t[p]) then
      t[p], t[up] = t[up], t[p]
    end
    if up - lo == 2 then
      break
    end
    local pivot = t[p]
    t[p], t[up - 1] = t[up - 1], t[p]
    local i, j = lo, up - 1
    while true do
      i = i + 1
      while lt(t[i], pivot) do
        i = i + 1
      end
      j = j - 1
      while lt(pivot, t[j]) do
        j = j - 1
      end
      if j < i then
        break
      end
      t[i], t[j] = t[j], t[i]
    end
    t[up - 1], t[i] = t[i], t[up - 1]
    if i - lo < up - i then
      auxsort(t, lo, i - 1, lt)
      lo = i + 1
    else
      auxsort(t, i + 1, up, lt)
      up = i - 1
    end
  end
end

function table.sort(t, lt)
  auxsort(t, 1, #t, lt or less)
end
