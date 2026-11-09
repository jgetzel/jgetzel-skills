-- Lua specs: what a CLI test can't reach (races, pure functions). Run: luajit swarm/lua/test/run.lua
-- Each *_spec.lua is a plain script of asserts; it passes if it returns without an error.
local dir = (arg[0]:match("^(.*)/[^/]*$") or ".")
local tree = (os.getenv("XDG_DATA_HOME") or ((os.getenv("HOME") or "") .. "/.local/share")) .. "/swarm/lua"
package.path = dir .. "/../?.lua;" .. tree .. "/share/lua/5.1/?.lua;" .. package.path  -- as the swarm-lua launcher does
package.cpath = tree .. "/lib/lua/5.1/?.so;" .. package.cpath
local lfs = require "lfs"
local specs = {}
for f in lfs.dir(dir) do
  if f:match("_spec%.lua$") then specs[#specs + 1] = f end
end
table.sort(specs)
local failed = 0
for _, f in ipairs(specs) do
  local ok, err = xpcall(dofile, debug.traceback, dir .. "/" .. f)
  if ok then print("ok    " .. f) else failed = failed + 1; print("FAIL  " .. f .. "\n" .. tostring(err)) end
end
print(("%d specs, %d failed"):format(#specs, failed))
os.exit(failed == 0 and 0 or 1)
