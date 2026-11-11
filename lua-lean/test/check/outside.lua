-- lua-lean check's test: each kind of construct outside the subset once (check.sh compares test/check/outside.out)
local bit = require("bit")
local ffi = require "ffi"
local M = {}

function M.add(a, b)
  return a + b
end

local function band(x, y)
  return bit.band(x, y)
end

function M.same(a, b)
  local mt = {
    __eq = function() return true end,
  }
  return setmetatable({}, mt) == setmetatable({}, mt)
end

function M:name(s)
  return ("%s %u"):format(s, 1), jit.version, string.dump, _G.newproxy, love
end

M.rep = function(s, n) return string.rep(s, n) end
function M.misc()
  return load("return 1", "x", "t", {}), io.open("x"), require("no.such.module")
end

function M.loop()
  for i = 1, 3 do
    if i == 2 then goto continue end
    if i == 3 then goto back end
    ::back::
    local _ = i
    ::continue::
  end
end

function M.dbg(f)
  return debug.getinfo(1, "l"), debug.traceback("x"), debug.getlocal(1, 1), xpcall(f, debug.traceback),
    debug.getmetatable(f), debug.getinfo(f, "u").nups
end

return M
