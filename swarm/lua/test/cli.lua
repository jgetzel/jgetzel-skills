-- CLI test harness: the Lua twin of test_swarm.py's class T. A cli_*_spec.lua returns a table of named tests
--   local T = {}
--   function T.test_x(t) t:sw("a", "task", "add", "t1"); t:eq(t:q1("select state from task").state, "open") end
--   return T
-- gets, per test, a fresh fixture t from run.lua (luajit swarm/lua/test/run.lua [pattern]), failures reported by name.
--
-- Fixture fields: t.d (temp dir), t.repo (git repo on main: a.txt b.txt "x", e.txt "mod (p, q)\n"), t.wt (worktree on
-- branch w2), t.db, t.cwd ({a = repo, b = wt}; add more), t.fakebin and t.launch (set by fakes/live_hc/fake).
-- Running things (r = {stdout=, stderr=, code=}):
--   t:sw(who, args..., [opts])  swarm as SWARM_NAME=who in t.cwd[who] (else t.repo); opts: ok (default true: asserts
--                               code 0), stdin, hc (HC_TERMINAL_ID; unset otherwise), cwd, env (extra vars, false unsets)
--   t:hook(who, ev, payload, hc) swarm hook <ev> with payload as JSON (cwd defaults); hookSpecificOutput or {}
--   t:edit(who, path)            pre-tool Edit of t.cwd[who]/path
--   t:exec(argv, opts)           any command (proc.exec opts); t:git(cwd, args...) git as user t, asserting success
-- Db: t:q(sql, ...) rows keyed by column name (NULL is nil: alias count(*) etc.), t:q1 the first row,
--   t:agent(name, {col = v}) joins then sets columns.
-- Files and conflicts: t:write(who, path, text), t:tick() (watchd --once), t:notices(who),
--   t:land(path, text) (a peer's PR lands on origin/main and t.repo fetches it).
-- Fakes: t:fakes() puts fake hc, gh and launch script in place; t:set_hc(terminal, ...) (none: hc ls fails),
--   t:set_gh(sub, out) (nil: gh <sub> fails; a table is JSON-encoded), t:calls(name) logged argv lines,
--   t:launched() {argv=, task={{owner, state}...}} per launch, t:live_hc(addr, ...) an hc whose ls shows these live,
--   t:fake(name, body) any executable in t.fakebin.
-- Asserts (msg optional): t:eq(got, want) deep, t:has(s, sub) / t:hasnt(s, sub) plain substring (or list member).
-- Cleanup: t:defer(fn) runs after the test; the temp dir is removed when the test passes, kept when it fails.
local proc, json, util = require "swarm.proc", require "swarm.json", require "swarm.util"
local db = require "swarm.db"
local stdlib = require "posix.stdlib"
local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
local M = {}
M.SWARM = os.getenv("SWARM_CLI") or stdlib.realpath(here .. "/../../swarm")
M.PATH = os.getenv("PATH")  -- before any spec puts its own fakes on PATH
local T = {}
T.__index = T

local function repr(v, seen)
  if type(v) == "string" then return ("%q"):format(v) end
  if type(v) ~= "table" then return tostring(v) end
  local keys, out = {}, {}
  for k in pairs(v) do keys[#keys + 1] = k end
  table.sort(keys, function(a, b) return tostring(a) < tostring(b) end)
  for _, k in ipairs(keys) do out[#out + 1] = (type(k) == "number" and "" or (k .. "=")) .. repr(v[k]) end
  return "{" .. table.concat(out, ", ") .. "}"
end
M.repr = repr

local function deq(a, b)
  if type(a) ~= "table" or type(b) ~= "table" then return a == b end
  for k, v in pairs(a) do if not deq(v, b[k]) then return false end end
  for k in pairs(b) do if a[k] == nil then return false end end
  return true
end

function T:eq(got, want, msg)
  if not deq(got, want) then error(("%s\n  got  %s\n  want %s"):format(msg or "not equal", repr(got), repr(want)), 2) end
end

local function has(s, sub)
  if type(s) == "table" then
    for _, x in ipairs(s) do if deq(x, sub) then return true end end
    return false
  end
  return type(s) == "string" and s:find(sub, 1, true) ~= nil
end

function T:has(s, sub, msg)
  if not has(s, sub) then error(("%s\n  %s\n  not in %s"):format(msg or "missing", repr(sub), repr(s)), 2) end
end

function T:hasnt(s, sub, msg)
  if has(s, sub) then error(("%s\n  %s\n  is in %s"):format(msg or "unexpected", repr(sub), repr(s)), 2) end
end

function T:defer(fn) self.cleanups[#self.cleanups + 1] = fn end

function T:exec(argv, o)
  local out, err, code = proc.exec(argv, o)
  return { stdout = out, stderr = err, code = code }
end

function T:git(cwd, ...)
  local r = self:exec({ "git", "-c", "user.name=t", "-c", "user.email=t@t", ... }, { cwd = cwd })
  if r.code ~= 0 then error("git " .. table.concat({ ... }, " ") .. ": " .. r.stderr, 2) end
  return r.stdout
end

function T:sw(who, ...)
  local args, o = { M.SWARM, ... }, {}
  if type(args[#args]) == "table" then o = table.remove(args) end
  local env = { SWARM_DB = self.db, SWARM_NAME = who, HC_TERMINAL_ID = o.hc or false,
                PATH = self.fakebin and (self.fakebin .. ":" .. M.PATH) or M.PATH, SWARM_LAUNCH = self.launch }
  for k, v in pairs(o.env or {}) do env[k] = v end
  -- an agent's own terminal would make `hc ls` part of the test
  local r = self:exec(args, { env = env, input = o.stdin, cwd = o.cwd or self.cwd[who] or self.repo })
  if o.ok ~= false and r.code ~= 0 then
    error(("swarm %s exited %d: %s%s"):format(table.concat(args, " ", 2), r.code, r.stderr, r.stdout), 2)
  end
  return r
end

function T:hook(who, ev, payload, hc)
  payload = payload or {}
  payload.cwd = payload.cwd or self.cwd[who] or self.repo
  local r = self:sw(who, "hook", ev, { stdin = json.encode(payload), hc = hc })
  if util.strip(r.stdout) == "" then return {} end
  return json.decode(r.stdout).hookSpecificOutput
end

function T:edit(who, path)
  return self:hook(who, "pre-tool", { tool_name = "Edit", tool_input = { file_path = self.cwd[who] .. "/" .. path } })
end

function T:q(sql, ...)
  stdlib.setenv("SWARM_DB", self.db)
  local c = db.connect()
  local rows = c:all(sql, ...)
  c.h:close()
  return rows
end

function T:q1(sql, ...) return self:q(sql, ...)[1] end

function T:agent(name, kw)
  self:sw(name, "join")
  for k, v in pairs(kw or {}) do self:q(("update agent set %s=? where name=?"):format(k), v, name) end
end

local function put(path, text, mode)
  local f = assert(io.open(path, "w"))
  f:write(text); f:close()
  if mode then os.execute("chmod " .. mode .. " " .. util.shquote(path)) end
end

function T:write(who, path, text) put(self.cwd[who] .. "/" .. path, text) end

function T:tick() self:sw("a", "watchd", "--once") end

function T:notices(who) return self:q("select body from msg where dest=? and kind='notice'", who) end

function T:land(path, text)
  local o, pr = self.d .. "/origin.git", self.d .. "/pr"
  if not util.slurp(o .. "/HEAD") then
    self:git(nil, "clone", "-q", "--bare", self.repo, o)
    self:git(self.repo, "remote", "add", "origin", o)
  end
  self:git(nil, "clone", "-q", o, pr)
  put(pr .. "/" .. path, text)
  self:git(pr, "commit", "-qam", "pr")
  self:git(pr, "push", "-q", "origin", "main")
  os.execute("rm -rf " .. util.shquote(pr))
  self:git(self.repo, "fetch", "-q", "origin")
end

-- ---- fakes for the external commands: hc, gh and the launch script (SWARM_LAUNCH) ----
function T:fake(name, body)
  self.fakebin = self.fakebin or (self.d .. "/fb")
  os.execute("mkdir -p " .. util.shquote(self.fakebin))
  put(self.fakebin .. "/" .. name, body, "755")
  return self.fakebin .. "/" .. name
end

-- hc ls answers from set_hc (absent: hc fails); gh answers from set_gh by subcommand (absent: fails); the launch
-- script logs its argv and the task row it saw. Every call is logged to <name>.log in the test dir.
function T:fakes()
  local D = util.shquote(self.d)
  self:fake("hc", "#!/bin/sh\necho \"$*\" >> " .. D .. "/hc.log\nif [ \"$1\" = ls ]; then\n  [ -f " .. D ..
    "/hc.json ] || exit 1\n  cat " .. D .. "/hc.json; echo\nelse echo '{}'; fi\n")
  self:fake("gh", "#!/bin/sh\necho \"$*\" >> " .. D .. "/gh.log\n[ -f " .. D .. "/gh.\"$1\" ] || exit 1\ncat " .. D ..
    "/gh.\"$1\"\n")
  self.launch = self.d .. "/launch"
  put(self.launch, ([[#!/usr/bin/env luajit
local D = %q
local f = io.open(D .. "/launch.log", "a"); f:write(table.concat(arg, " ") .. "\n"); f:close()
local sqlite3, cjson = require "lsqlite3", require "cjson"
local h, rows, argv = sqlite3.open(os.getenv("SWARM_DB")), {}, {}
for r in h:rows("select owner,state from task") do rows[#rows + 1] = { r[1] or cjson.null, r[2] or cjson.null } end
for i = 1, #arg do argv[i] = arg[i] end
f = io.open(D .. "/launch.calls", "a"); f:write(cjson.encode({ argv = argv, task = rows }) .. "\n"); f:close()
if io.open(D .. "/launch.fail") then io.stderr:write("no Herdr window\nmore\n"); os.exit(1) end
print("hc1")
]]):format(self.d), "755")
end

-- hc ls --json lists these terminals ({address=, ...}, state live unless given); none given: hc ls fails.
function T:set_hc(...)
  local f, ts = self.d .. "/hc.json", {}
  if select("#", ...) == 0 then os.remove(f) return end
  for i, x in ipairs({ ... }) do
    ts[i] = { state = "live" }
    for k, v in pairs(x) do ts[i][k] = v end
  end
  put(f, json.encode({ terminals = ts }))
end

-- gh <sub> prints out; nil: it fails (rate limited).
function T:set_gh(sub, out)
  local f = self.d .. "/gh." .. sub
  if out == nil then os.remove(f) else put(f, type(out) == "string" and out or json.encode(out)) end
end

function T:calls(name)
  local s = util.slurp(self.d .. "/" .. name .. ".log")
  return s and util.splitlines(s) or {}
end

function T:launched()
  local s, r = util.slurp(self.d .. "/launch.calls"), {}
  for _, l in ipairs(s and util.splitlines(s) or {}) do r[#r + 1] = json.decode(l) end
  return r
end

-- fencing on the bound terminal (sw-ownership §7.2): an hc whose ls shows these terminals live
function T:live_hc(...)
  local ts = {}
  for i, x in ipairs({ ... }) do ts[i] = { address = x, state = "live" } end
  self:fake("hc", "#!/bin/sh\n[ \"$1\" = ls ] && echo '" .. json.encode({ terminals = ts }) .. "' || echo '{}'\n")
end

function M.new()
  local t = setmetatable({ cleanups = {} }, T)
  t.d = stdlib.mkdtemp((os.getenv("TMPDIR") or "/tmp") .. "/swarm-cli-XXXXXX")
  t.repo, t.wt, t.db = t.d .. "/repo", t.d .. "/wt", t.d .. "/swarm.db"
  os.execute("mkdir " .. util.shquote(t.repo))
  t:git(t.repo, "init", "-q", "-b", "main")
  put(t.repo .. "/a.txt", "x"); put(t.repo .. "/b.txt", "x"); put(t.repo .. "/e.txt", "mod (p, q)\n")
  t:git(t.repo, "add", ".")
  t:git(t.repo, "commit", "-qm", "init")
  t:git(t.repo, "worktree", "add", "-q", "-b", "w2", t.wt)
  t.cwd = { a = t.repo, b = t.wt }
  return t
end

function T:cleanup(passed)
  for i = #self.cleanups, 1, -1 do pcall(self.cleanups[i]) end
  if passed then os.execute("rm -rf " .. util.shquote(self.d)) end
end

return M
