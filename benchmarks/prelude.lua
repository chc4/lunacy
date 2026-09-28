-- Library functions in Lua, each defined only where the running Lua lacks it:
-- `tools/bundle_bench.py` puts this before every benchmark.

-- Lua 5.1's `table.sort` (ltablib.c's `auxsort`): a quicksort on the median of
-- three, recursing into the smaller part and looping on the larger. Lunacy's
-- natives can't call a Lua comparator.
if not table.sort then
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
end

-- The benchmark suite's `io.write_devnull`: `io.write` with the output thrown
-- away, which a benchmark calls to use its results.
if not io.write_devnull then
  function io.write_devnull() end
end
