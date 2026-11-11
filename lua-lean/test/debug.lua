-- the debug library without a call stack: raw metatables, a closure's upvalues, getinfo of a function
local M = {}

-- the metatable whatever __metatable hides
function M.rawmeta(o)
  return debug.getmetatable(o)
end

-- a counter and a way to reset it from outside
function M.counter()
  local n = 0
  local function inc() n = n + 1; return n end
  return inc
end

function M.reset(f, v)
  local name = debug.getupvalue(f, 1)
  if name == "n" then debug.setupvalue(f, 1, v) end
  return name
end

function M.arity(f)
  local i = debug.getinfo(f, "u")
  return i.nparams, i.isvararg, i.nups
end

-- an error value that is not a string comes back as it is
function M.handler(e)
  return debug.traceback(e)
end

return M
