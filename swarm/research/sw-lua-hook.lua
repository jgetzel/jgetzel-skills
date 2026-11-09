#!/usr/bin/env luajit
-- sw-lua prototype: `swarm hook pre-tool` for Bash (non-heavy) and Edit, ported line for line from swarm/swarm
-- to time it against Python (sw-lua.md §7). Not the port: no SendMessage, heavy-build note, shared-tree notice or fenced-event dedup.
-- Usage: SWARM_DB=<copy> SWARM_NAME=x luajit sw-lua-hook.lua < payload.json
local sqlite3, cjson, rex = require "lsqlite3", require "cjson", require "rex_pcre2"
local unistd, wait, stdlib = require "posix.unistd", require "posix.sys.wait", require "posix.stdlib"
local fnm = require "posix.fnmatch"

local SCHEMA = [[
create table if not exists agent(name text primary key, hc text, model text, cwd text, status text,
  last_active int, ctx_tokens int default 0, compacted_at int default 0, started int, ended int, snap text,
  waiter int, wt text);
create table if not exists msg(id integer primary key autoincrement, ts int, frm text, dest text,
  body text, urgent int default 0, kind text);
create table if not exists cursor(agent text primary key, last_msg_id int default 0);
create table if not exists task(id integer primary key autoincrement, title text, body text,
  state text default 'open', owner text, lease_until int, created_by text, evidence text, deps text, model text, question text);
create table if not exists lock(path text primary key, agent text, reason text, since int, lease_until int, seen int default 0);
create table if not exists conflict(a text, b text, path text, since int, primary key(a,b,path));
create table if not exists pairkey(a text, b text, key text, primary key(a,b));
create table if not exists meta(k text primary key, v text);
create table if not exists event(id integer primary key autoincrement, ts int, agent text, kind text,
  path text, data text);
create table if not exists ci(id integer primary key, sha text, status text, conclusion text, url text,
  created text, updated text, failed text);
]]

local function now() return os.time() end

-- stdout of argv, or nil on a nonzero exit; stderr discarded (Python run()).
local function run(argv, cwd)
  local r, w = unistd.pipe()
  local pid = unistd.fork()
  if pid == 0 then
    unistd.dup2(w, 1)
    local null = require("posix.fcntl").open("/dev/null", require("posix.fcntl").O_WRONLY)
    unistd.dup2(null, 2)
    unistd.close(r); unistd.close(w)
    if cwd and not unistd.chdir(cwd) then unistd._exit(127) end
    unistd.execp(argv[1], { select(2, unpack(argv)) })
    unistd._exit(127)
  end
  unistd.close(w)
  local out = {}
  while true do
    local s = unistd.read(r, 65536)
    if not s or #s == 0 then break end
    out[#out + 1] = s
  end
  unistd.close(r)
  local _, how, code = wait.wait(pid)
  return (how == "exited" and code == 0) and table.concat(out) or nil
end

local function git(args, cwd)
  local o = run({ "git", unpack(args) }, cwd)
  return o and (o:gsub("%s+$", "")) or nil
end

local function connect()
  local db = assert(sqlite3.open(os.getenv("SWARM_DB")))
  db:busy_timeout(10000)
  db:exec("pragma journal_mode=wal")
  assert(db:exec(SCHEMA) == sqlite3.OK, db:errmsg())
  -- the Python connect() also checks 16 columns with pragma table_info; one pass does the same work here
  local cols = {}
  for r in db:nrows("pragma table_info(task)") do cols[r.name] = true end
  for r in db:nrows("pragma table_info(agent)") do cols["agent." .. r.name] = true end
  return db
end

local function one(db, sql, ...)
  local st = assert(db:prepare(sql), db:errmsg())
  st:bind_values(...)
  for r in st:nrows() do st:finalize(); return r end
  st:finalize()
end

local function exec(db, sql, ...)
  local st = assert(db:prepare(sql), db:errmsg())
  st:bind_values(...)
  st:step(); st:finalize()
end

local function hhmm(t) return os.date("%H:%M", t) end

local function fence(db, name)
  local r = one(db, "select hc, ended from agent where name=?", name)
  if not r then return nil end
  if r.ended then return name .. " was ended at " .. hhmm(r.ended) .. "; `swarm join` to return." end
  local here = os.getenv("HC_TERMINAL_ID")
  if r.hc and r.hc ~= here then
    return ("%s is bound to %s; this terminal is %s. `swarm join --takeover` moves it here."):format(name, r.hc, here or "outside Herdr")
  end
end

local function touch(db, name, cwd)
  if fence(db, name) then return end
  local here = os.getenv("HC_TERMINAL_ID")
  exec(db, "insert or ignore into agent(name,cwd,status,last_active,started,hc) values(?,?,?,?,?,?)", name, cwd, "idle", now(), now(), here)
  exec(db, "update agent set cwd=? where name=? and ended is null and (hc is null or hc is ?)", cwd, name, here)
end

local function emit(event, ctx, deny)
  local o = { hookEventName = event }
  if deny then o.permissionDecision, o.permissionDecisionReason = "deny", deny end
  if ctx then o.additionalContext = ctx end
  io.write(cjson.encode { hookSpecificOutput = o }, "\n")
end

local NOT_HEAVY = rex.new([[^\s*(git|gh|swarm|echo|grep|rg|cat|ls|sed|head|tail)\b]])
local HEAVY = rex.new([[\b(cabal|stack|ghc|make|cmake|ninja|gradle|mvn|pytest|tox|tsc|spago|purs|playwright]] ..
  [[|nix\s+(build|flake\s+check)|docker\s+build|(cargo|go|npm|pnpm|yarn|bun)\s+(run\s+)?(build|test|check|clippy|bench|install))\b]])

local function is_heavy(cmd, cwd)
  if rex.find(cmd, [[^\s*swarm\s+run\b]]) then return true end
  if NOT_HEAVY:find(cmd) then return false end
  local pats = { HEAVY }
  local top = git({ "rev-parse", "--show-toplevel" }, cwd)
  local f = top and io.open(top .. "/.claude/swarm.json")
  if f then
    local okj, j = pcall(cjson.decode, f:read("*a")); f:close()
    for _, x in ipairs(okj and type(j) == "table" and type(j.heavy) == "table" and j.heavy or {}) do
      local okr, r = pcall(rex.new, x)
      if okr then pats[#pats + 1] = r end
    end
  end
  for _, r in ipairs(pats) do if r:find(cmd) then return true end end
  return false
end

local function dirname(p) return p:match("^(.*)/[^/]*$") or "" end

local function repo_rel(path, cwd)
  local p = path:sub(1, 1) == "/" and path or ((cwd or ".") .. "/" .. path)
  local d = dirname(p)
  while d ~= "" and not stdlib.realpath(d) do d = dirname(d) end
  d = stdlib.realpath(d ~= "" and d or cwd)
  p = d .. p:sub(#dirname(p) + 1)  -- shortcut: realpath of the deepest existing dir only, fine for a timing probe
  local top = git({ "rev-parse", "--show-toplevel" }, d)
  if not top then return nil end
  top = stdlib.realpath(top)
  if p:sub(1, #top + 1) ~= top .. "/" then return nil end
  return top, p:sub(#top + 2)
end

local function covers(path, pat)
  local base = pat:gsub("/+$", "")
  return fnm.fnmatch(pat, path) == 0 or path:sub(1, #base + 1) == base .. "/"
end

local name = os.getenv("SWARM_NAME")
local okj, p = pcall(cjson.decode, io.read("*a"))
if not okj or type(p) ~= "table" then p = {} end
if not name then return end
local db = connect()
local cwd = (type(p.cwd) == "string" and p.cwd ~= "") and p.cwd or unistd.getcwd()
local tool, ti = p.tool_name, type(p.tool_input) == "table" and p.tool_input or {}
if fence(db, name) then return end
touch(db, name, cwd)
local t = now()
if tool == "Bash" then
  local cmd = type(ti.command) == "string" and ti.command or ""
  if is_heavy(cmd, cwd) then
    emit("PreToolUse", "machine note skipped in the prototype")
    exec(db, "insert into event(ts,agent,kind,path,data) values(?,?,?,?,?)", t, name, "heavy-start", nil, cmd:sub(1, 80))
  end
elseif tool == "Edit" or tool == "Write" or tool == "MultiEdit" or tool == "NotebookEdit" then
  local top, path = repo_rel(ti.file_path or ti.notebook_path or "", cwd)
  if not top then return end
  local st = db:prepare("select l.* from lock l join agent a on a.name=l.agent where l.agent!=? and l.lease_until>? and a.ended is null")
  st:bind_values(name, t)
  for lk in st:nrows() do
    if covers(path, lk.path) then
      st:finalize()
      exec(db, "insert into event(ts,agent,kind,path,data) values(?,?,?,?,?)", t, name, "deny-lock", path, lk.agent)
      return emit("PreToolUse", nil, ("%s is locked by %s since %s. Ask it with SendMessage."):format(path, lk.agent, hhmm(lk.since)))
    end
  end
  st:finalize()
  exec(db, "update agent set wt=? where name=?", top, name)
end
