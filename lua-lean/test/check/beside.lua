-- lua-lean check's test (check.sh): a module beside the script is source, and an error of level 2 has the chunk's place
local util = require("util")
local M = {}

function M.double(x)
  return util.num(x) * 2
end

function M.num(x)
  return util.num(x)
end

function M.bad(x)
  error("bad " .. type(x), 2)
end

return M
