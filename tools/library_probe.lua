-- Prints every global, and each member of every global table, one name a line (`string.rep`), as
-- the runtime running it has them. Used by tools/library_gaps.py.
for name, value in pairs(_G) do
  print(name)
  if type(value) == "table" and value ~= _G then
    for member in pairs(value) do
      if type(member) == "string" then print(name .. "." .. member) end
    end
  end
end
