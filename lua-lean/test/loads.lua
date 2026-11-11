-- load, loadstring, dofile and require: lifted with the chunks loadstring and load make from constants
local add = loadstring("local a, b = ...\nreturn a + b", "=add")
local twice = load("return 2 * ...")
local function run(src)
  local f, err = loadstring(src)
  if not f then return nil, err end
  return pcall(f)
end
package.path = "test/?.lua;" .. package.path
local j = require "mods.j"
local g = { dofile("test/mods/g.lua") }
return add(1, 2), twice(4), run("return 1"), j.f(21), #g
