#!/usr/bin/env luajit
-- JSON helpers for probe.sh.
--   probe-json.lua get EXPR            (JSON on stdin as d) print the Lua expression EXPR, e.g. d.result.tab.id
--   probe-json.lua settings CMD...     print a settings.json whose PreToolUse hook runs the quoted CMD
local d = (arg[0]:match("^(.*)/[^/]*$") or ".")
package.path = d .. "/?.lua;" .. d .. "/../swarm/lua/?.lua;" .. package.path
local json, util = require "swarm.json", require "swarm.util"

if arg[1] == "get" then
  local doc = assert(json.decode(io.read("*a")))
  local v = assert(load("local d = ...; return " .. arg[2]))(doc)
  print(v == nil and "" or tostring(v))
elseif arg[1] == "settings" then
  local cmd = util.shjoin({ unpack(arg, 2) })
  print(json.encode({ hooks = { PreToolUse = { { matcher = "", hooks = { { type = "command", command = cmd, timeout = 10 } } } } } }))
else
  io.stderr:write("usage: probe-json.lua get EXPR | settings CMD...\n"); os.exit(2)
end
