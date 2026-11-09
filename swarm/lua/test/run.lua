-- Lua specs. Run: luajit swarm/lua/test/run.lua [pattern]  (pattern: a plain substring of a spec file or test name)
-- Runs one worker process per plain spec and per cli test, JOBS (SWARM_TEST_JOBS, 8) at a time; a test running past SWARM_TEST_TIMEOUT (60s) is killed and reported as HUNG by name.
-- A *_spec.lua is a plain script of asserts: it passes if it returns without an error. A cli_*_spec.lua returns a
-- table of named tests, each run with a fresh CLI fixture (cli.lua's header documents it) and reported by name.
local dir = (arg[0]:match("^(.*)/[^/]*$") or ".")
local tree = (os.getenv("XDG_DATA_HOME") or ((os.getenv("HOME") or "") .. "/.local/share")) .. "/swarm/lua"
package.path = dir .. "/../?.lua;" .. tree .. "/share/lua/5.1/?.lua;" .. package.path  -- as the swarm launcher does
package.cpath = tree .. "/lib/lua/5.1/?.so;" .. package.cpath
local lfs = require "lfs"
local cli = require "test.cli"  -- loaded first: it keeps PATH from before any spec puts fakes on it
local one = arg[1] == "--one"  -- worker mode: --one <spec file> [test name]
local pat = not one and arg[1] or nil
local function match(s) return not pat or s:find(pat, 1, true) end
local specs = {}
for f in lfs.dir(dir) do
  if f:match("_spec%.lua$") then specs[#specs + 1] = f end
end
table.sort(specs)
local function q(s) return "'" .. s:gsub("'", "'\\''") .. "'" end
if one then
  local f, k = arg[2], arg[3]
  local ok, err
  if not k then ok, err = xpcall(dofile, debug.traceback, dir .. "/" .. f)
  else
    local t = cli.new()
    ok, err = xpcall(dofile(dir .. "/" .. f)[k], debug.traceback, t)
    t:cleanup(ok)
    if not ok then err = err .. "\n  (fixture kept: " .. t.d .. ")" end
  end
  if not ok then io.stderr:write(tostring(err), "\n") end
  os.exit(ok and 0 or 1)
end
-- Coordinator: one worker process per plain spec and per cli test, run in parallel under a per-test timeout.
local TIMEOUT = tonumber(os.getenv("SWARM_TEST_TIMEOUT")) or 60
local JOBS = tonumber(os.getenv("SWARM_TEST_JOBS")) or 8
local jobs = {}
local failed, ran = 0, 0
local function report(ok, name, err)
  ran = ran + 1
  if ok then print("ok    " .. name) else failed = failed + 1; print("FAIL  " .. name .. "\n" .. tostring(err)) end
end
for _, f in ipairs(specs) do
  if not f:match("^cli_") then
    if match(f) then jobs[#jobs + 1] = {name = f, f = f} end
  else
    local ok, tests = xpcall(dofile, debug.traceback, dir .. "/" .. f)
    if not ok then report(false, f, tests) else
      local names = {}
      for k in pairs(tests) do if match(f) or match(k) then names[#names + 1] = k end end
      table.sort(names)
      for _, k in ipairs(names) do jobs[#jobs + 1] = {name = f .. " " .. k, f = f, k = k} end
    end
  end
end
local tmp = os.tmpname(); os.remove(tmp); os.execute("mkdir -p " .. q(tmp))
local list = assert(io.open(tmp .. "/jobs", "w"))
for i, j in ipairs(jobs) do
  list:write(("timeout -s KILL %d luajit %s --one %s %s >%s/%d.out 2>&1; echo $? >%s/%d.rc\n"):format(
    TIMEOUT, q(arg[0]), q(j.f), j.k and q(j.k) or "", tmp, i, tmp, i))
end
list:close()
os.execute(("xargs -d '\\n' -P %d -n1 sh -c 'eval \"$0\"' <%s/jobs"):format(JOBS, tmp))
for i, j in ipairs(jobs) do
  local rc = assert(io.open(("%s/%d.rc"):format(tmp, i)), "worker never ran: " .. j.name):read("*a"):match("%d+")
  local out = io.open(("%s/%d.out"):format(tmp, i)):read("*a")
  if rc == "137" then out = ("HUNG: killed after %ds with no result\n"):format(TIMEOUT) .. out end
  report(rc == "0", j.name, rc ~= "0" and out or nil)
end
os.execute("rm -rf " .. q(tmp))
print(("%d run, %d failed"):format(ran, failed))
os.exit(failed == 0 and ran > 0 and 0 or 1)
