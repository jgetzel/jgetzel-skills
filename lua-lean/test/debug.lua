-- the debug library: raw metatables, a closure's upvalues, getinfo of a function or of a level of the stack, tracebacks
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

-- the line its caller is at, and a function's lines
function M.caller()
  local i = debug.getinfo(2, "l")
  return i.currentline
end

function M.lines(f)
  local i = debug.getinfo(f, "S")
  return i.linedefined, i.lastlinedefined
end

-- an error's traceback, from its handler
function M.trace(f)
  return xpcall(f, debug.traceback)
end

return M
