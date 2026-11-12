-- the module beside test/check/beside.lua: an error of level 2 has its caller's place
local M = {}

function M.num(x)
  if type(x) ~= "number" then error("number expected, got " .. type(x), 2) end
  return x
end

return M
