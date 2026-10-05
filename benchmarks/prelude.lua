-- Library functions in Lua, each defined only where the running Lua lacks it:
-- `tools/bundle_bench.py` puts this before every benchmark.

-- The benchmark suite's `io.write_devnull`: `io.write` with the output thrown
-- away, which a benchmark calls to use its results. Luau has no `io`.
if not (io and io.write_devnull) then
  io = io or {}
  io.write_devnull = function() end
end

-- Lua 5.1's global `unpack`, which later Luas have as `table.unpack` only.
unpack = unpack or table.unpack
