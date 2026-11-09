-- Lua specs. Run: luajit swarm/lua/test/run.lua [pattern]  (pattern: a plain substring of a spec file or test name)
-- A *_spec.lua is a plain script of asserts: it passes if it returns without an error. A cli_*_spec.lua returns a
-- table of named tests, each run with a fresh CLI fixture (cli.lua's header documents it) and reported by name.
local dir = (arg[0]:match("^(.*)/[^/]*$") or ".")
local tree = (os.getenv("XDG_DATA_HOME") or ((os.getenv("HOME") or "") .. "/.local/share")) .. "/swarm/lua"
package.path = dir .. "/../?.lua;" .. tree .. "/share/lua/5.1/?.lua;" .. package.path  -- as the swarm launcher does
package.cpath = tree .. "/lib/lua/5.1/?.so;" .. package.cpath
local lfs = require "lfs"
local cli = require "test.cli"  -- loaded first: it keeps PATH from before any spec puts fakes on it
local pat = arg[1]
local function match(s) return not pat or s:find(pat, 1, true) end
local specs = {}
for f in lfs.dir(dir) do
  if f:match("_spec%.lua$") then specs[#specs + 1] = f end
end
table.sort(specs)
local failed, ran = 0, 0
local function report(ok, name, err)
  ran = ran + 1
  if ok then print("ok    " .. name) else failed = failed + 1; print("FAIL  " .. name .. "\n" .. tostring(err)) end
end
for _, f in ipairs(specs) do
  if not f:match("^cli_") then
    if match(f) then
      local ok, err = xpcall(dofile, debug.traceback, dir .. "/" .. f)
      report(ok, f, err)
    end
  else
    local ok, tests = xpcall(dofile, debug.traceback, dir .. "/" .. f)
    if not ok then report(false, f, tests) else
      local names = {}
      for k in pairs(tests) do if match(f) or match(k) then names[#names + 1] = k end end
      table.sort(names)
      for _, k in ipairs(names) do
        local t = cli.new()
        local tok, err = xpcall(tests[k], debug.traceback, t)
        t:cleanup(tok)
        report(tok, f .. " " .. k, not tok and (err .. "\n  (fixture kept: " .. t.d .. ")") or nil)
      end
    end
  end
end
print(("%d run, %d failed"):format(ran, failed))
os.exit(failed == 0 and ran > 0 and 0 or 1)
