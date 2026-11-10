-- The per-repo sqlite db: schema and column migrations, queries, tx, the event log.
local sqlite3 = require "lsqlite3"
local lfs = require "lfs"
local util = require "swarm.util"
local proc = require "swarm.proc"
local M = {}

M.SCHEMA = [[
create table if not exists agent(name text primary key, hc text, model text, cwd text, status text,
  last_active int, ctx_tokens int default 0, compacted_at int default 0, started int, ended int, snap text,
  waiter int, wt text);
create table if not exists msg(id integer primary key autoincrement, ts int, frm text, dest text,
  body text, urgent int default 0, kind text);
create table if not exists cursor(agent text primary key, last_msg_id int default 0);
create table if not exists task(id integer primary key autoincrement, title text, body text,
  state text default 'open', owner text, lease_until int, created_by text, evidence text, deps text, model text, question text,
  effort text);
create table if not exists lock(path text primary key, agent text, reason text, since int, lease_until int, seen int default 0);
create table if not exists conflict(a text, b text, path text, since int, primary key(a,b,path));
create table if not exists pairkey(a text, b text, key text, primary key(a,b));
create table if not exists meta(k text primary key, v text);
create table if not exists event(id integer primary key autoincrement, ts int, agent text, kind text,
  path text, data text);
create table if not exists ci(id integer primary key, sha text, status text, conclusion text, url text,
  created text, updated text, failed text);
]]

-- dbs made before sw-locks
M.COLUMNS = { { "agent", "wt text" }, { "lock", "seen int default 0" }, { "task", "model text" }, { "task", "question text" },
  { "agent", "claude_pid int" }, { "task", "created_at int" }, { "task", "first_claimed_at int" }, { "task", "done_at int" },
  { "task", "dropped_at int" }, { "task", "pr int" }, { "task", "merged_at int" }, { "task", "ci_conclusion text" },
  { "task", "ci_green_at int" }, { "task", "claim_ctx int" }, { "task", "done_ctx int" }, { "task", "deps text" },
  { "ci", "workflow text" }, { "task", "answer text" }, { "task", "effort text" },
  { "agent", "role text" } }

local DB = {}
DB.__index = DB

-- lsqlite3 on LuaJIT binds every number as a double, so 5 lands in a text column as '5.0' (and Python, sharing
-- the db until the cutover, can't int() it). Integral numbers go into the SQL as literals instead; the rest bind.
local function prepare(c, sql, ...)
  local n, args, binds = select("#", ...), { ... }, {}
  local i, out, pos = 0, {}, 1
  while true do
    local q = sql:find("[?']", pos)
    if not q then break end
    if sql:sub(q, q) == "'" then  -- a string literal: skip to its close ('' is an escaped quote)
      local e = sql:find("'", q + 1, true)
      while e and sql:sub(e + 1, e + 1) == "'" do e = sql:find("'", e + 2, true) end
      out[#out + 1] = sql:sub(pos, e or #sql)
      pos = (e or #sql) + 1
    else
      i = i + 1
      local v = args[i]
      if v == true then v = 1 elseif v == false then v = 0 end
      out[#out + 1] = sql:sub(pos, q - 1)
      if type(v) == "number" and v == math.floor(v) and math.abs(v) < 2 ^ 53 then
        out[#out + 1] = v < 0 and ("(%d)"):format(v) or ("%d"):format(v)
      else
        out[#out + 1] = "?"
        binds[#binds + 1] = { v }
      end
      pos = q + 1
    end
  end
  out[#out + 1] = sql:sub(pos)
  if i ~= n then error(("sql: %d parameters, %d values: %s"):format(i, n, sql), 2) end
  local st = c.h:prepare(table.concat(out))
  if not st then error("sqlite: " .. c.h:errmsg() .. ": " .. sql, 3) end
  for k, b in ipairs(binds) do
    if b[1] == nil then st:bind(k) else st:bind(k, b[1]) end
  end
  return st
end

local function fail(c, st, sql)
  st:finalize()
  error("sqlite: " .. c.h:errmsg() .. ": " .. sql, 3)
end

-- Rows as tables keyed by column name; NULL is nil (so never read rows positionally).
-- all, and the column names too (state --json prints a NULL column as null, so it needs to know the columns).
function DB:all_cols(sql, ...)
  local st, rows = prepare(self, sql, ...), {}
  local names = st:get_names()
  while true do
    local rc = st:step()
    if rc == sqlite3.ROW then rows[#rows + 1] = st:get_named_values()
    elseif rc == sqlite3.DONE then break
    else fail(self, st, sql) end
  end
  st:finalize()
  return rows, names
end

function DB:all(sql, ...)
  return (self:all_cols(sql, ...))
end

function DB:one(sql, ...)
  return self:all(sql, ...)[1]
end

-- Runs one statement; returns the rows it changed (Python's rowcount).
function DB:exec(sql, ...)
  local st = prepare(self, sql, ...)
  local rc = st:step()
  if rc ~= sqlite3.DONE and rc ~= sqlite3.ROW then fail(self, st, sql) end
  st:finalize()
  return self.h:changes()
end

function DB:script(sql)
  if self.h:exec(sql) ~= sqlite3.OK then error("sqlite: " .. self.h:errmsg(), 2) end
end

function DB:last_id()
  return self.h:last_insert_rowid()
end

-- One `begin immediate` transaction (sw-ownership §4.1); nested calls join the outer one. Never run a subprocess
-- inside. fn's error (die is one) rolls back and goes on up; fn's return values come back.
function DB:tx(fn)
  if self.depth > 0 then return fn(self) end
  self:script("begin immediate")
  self.depth = 1
  local r = { pcall(fn, self) }
  self.depth = 0
  if not r[1] then
    self.h:exec("rollback")
    error(r[2], 0)
  end
  self:script("commit")
  return unpack(r, 2, table.maxn(r))
end

function DB:columns(tbl)
  local r = {}
  for _, x in ipairs(self:all("pragma table_info(" .. tbl .. ")")) do r[x.name] = true end
  return r
end

function M.dbpath()
  local p = os.getenv("SWARM_DB")
  if p and p ~= "" then return p end
  local d = proc.git({ "rev-parse", "--path-format=absolute", "--git-common-dir" })
  if not d or d == "" then util.die("not in a git repo and SWARM_DB is unset") end
  return util.join(d, "swarm", "swarm.db")
end

local function makedirs(d)
  if d == "" or lfs.attributes(d, "mode") then return end
  makedirs(util.dirname(d))
  lfs.mkdir(d)
end

function M.connect()
  local p = M.dbpath()
  makedirs(util.dirname(p))
  local h, _, err = sqlite3.open(p)
  if not h then util.die(("can't open %s: %s"):format(p, err)) end
  local c = setmetatable({ h = h, depth = 0, path = p }, DB)
  h:busy_timeout(10000)
  c:all("pragma journal_mode=wal")
  c:script(M.SCHEMA)
  local cols = {}
  for _, tc in ipairs(M.COLUMNS) do
    local tbl, col = tc[1], tc[2]
    cols[tbl] = cols[tbl] or c:columns(tbl)
    local name = col:match("^%S+")
    if not cols[tbl][name] then
      c:exec(("alter table %s add column %s"):format(tbl, col))
      cols[tbl][name] = true
    end
  end
  if cols.task.after then  -- one-time: task.after (one id) became task.deps
    c:tx(function()
      if c:columns("task").after then
        c:exec("update task set deps=after where deps is null and after is not null")
        c:exec("alter table task drop column after")
      end
    end)
  end
  return c
end

-- A read-only connection: no schema, no migrations, never creates the file. Nil and the error if it can't open.
function M.open_ro(p)
  local h, _, err = sqlite3.open(p, sqlite3.OPEN_READONLY)
  if not h then return nil, err end
  h:busy_timeout(10000)
  return setmetatable({ h = h, depth = 0, path = p }, DB)
end

function M.log(c, agent, kind, path, data)
  c:exec("insert into event(ts,agent,kind,path,data) values(?,?,?,?,?)", util.now(), agent, kind, path, data)
end

return M
