-- Errors as LuaJIT gives them: each with the place (chunk:line:) of the operator or call that raised it, or of the
-- caller `error`'s level names, and the names LuaJIT gives the operands. luajit errors.lua
local M = {}

function M.name(t)
  return t.name
end

function M.check(x)
  if type(x) ~= "number" then error("not a number: " .. tostring(x), 2) end
  return x
end

function M.safe(f, ...)
  local ok, e = pcall(f, ...)
  if ok then return e end
  return "failed: " .. tostring(e)
end

function M.sum(t)
  local s = 0
  for i = 1, #t do s = s + M.check(t[i]) end
  return s
end

if arg and arg[0] and arg[0]:match("errors%.lua$") then
  print(M.safe(M.name, nil), M.safe(M.sum, {1, "x"}), M.safe(M.sum, {1, 2}))
end

return M
