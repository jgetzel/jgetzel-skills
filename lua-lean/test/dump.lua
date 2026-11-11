-- string.dump and load of the dump: the function back, its upvalues new and nil, stripped or not
local M = {}

-- a copy of f that shares none of its upvalues
function M.copy(f)
  return load(string.dump(f))
end

-- a dump is a string; a load that wants text refuses it
function M.kind(f, strip)
  local d = string.dump(f, strip)
  return type(d), load(d, "=copy", "t")
end

function M.square(x)
  local function sq(y) return y * y end
  return load(string.dump(sq, true))(x)
end

-- the copy's upvalue is nil, so it counts from nothing
function M.fresh()
  local n = 0
  local function inc() n = (n or 10) + 1; return n end
  local again = load(string.dump(inc))
  return inc(), again(), again()
end

return M
