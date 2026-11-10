-- Paths and locks: repo_rel, covers, lock_holder, task_of; cmd lock/unlock.
local util, proc, db = require "swarm.util", require "swarm.proc", require "swarm.db"
local agents = require "swarm.agents"
local stdlib, lfs = require "posix.stdlib", require "lfs"
local fnmatch = require "posix.fnmatch"
local M = {}

-- os.path.realpath, non-strict: the longest existing prefix resolved, the rest appended.
-- shortcut: `..` is folded before symlinks are resolved (Python resolves first); fine for repo paths.
local function realpath(p)
  local parts = {}
  for x in p:gmatch("[^/]+") do
    if x == ".." then parts[#parts] = nil elseif x ~= "." then parts[#parts + 1] = x end
  end
  local tail = {}
  while true do
    local head = "/" .. table.concat(parts, "/")
    local r = stdlib.realpath(head)
    if r then
      if #tail == 0 then return r end
      return util.join(r, table.concat(tail, "/"))
    end
    table.insert(tail, 1, table.remove(parts))
  end
end

-- toplevel, repo-relative path for an absolute or cwd-relative path; nil outside a repo.
function M.repo_rel(path, cwd)
  local p = realpath(util.join(stdlib.realpath(".") or "/", cwd or ".", path))
  local d = util.dirname(p)
  while d ~= "/" and lfs.attributes(d, "mode") ~= "directory" do d = util.dirname(d) end
  local top = proc.git({ "rev-parse", "--show-toplevel" }, d)
  if not top or top == "" then return nil end
  top = realpath(top)
  if p == top then return top, "." end
  if util.startswith(p, top == "/" and "/" or top .. "/") then return top, p:sub(#top + (top == "/" and 1 or 2)) end
  return nil
end

-- Whether lock pattern pat covers path: a glob, or a directory prefix (`migrations/`).
function M.covers(path, pat)
  return path == pat or fnmatch.fnmatch(pat, path, 0) == 0 or util.startswith(path, (pat:gsub("/+$", "")) .. "/")
end

-- A glob as tokens: "*", "?", { c = char }, or { set = "..." } for a [...] class. As a directory, the pattern is a
-- literal prefix (covers' startswith) and then anything.
local function tokens(pat, dir)
  local r, i = {}, 1
  if dir then
    for ch in (pat:gsub("/+$", "") .. "/"):gmatch(".") do r[#r + 1] = { c = ch } end
    r[#r + 1] = "*"
    return r
  end
  while i <= #pat do
    local ch, j = pat:sub(i, i), pat:find("]", i + 2, true)
    if ch == "*" then
      if r[#r] ~= "*" then r[#r + 1] = "*" end
    elseif ch == "?" then r[#r + 1] = "?"
    elseif ch == "[" and j then r[#r + 1] = { set = pat:sub(i + 1, j - 1) }; i = j
    else
      if ch == "\\" and i < #pat then i = i + 1; ch = pat:sub(i, i) end
      r[#r + 1] = { c = ch }
    end
    i = i + 1
  end
  return r
end

local function one(a, b)  -- two single-character tokens can match one character (two classes: taken as yes)
  if a == "?" or b == "?" then return true end
  if a.c and b.c then return a.c == b.c end
  if a.set and b.set then return true end
  local set, ch = a.set or b.set, a.c or b.c
  return fnmatch.fnmatch("[" .. set .. "]", ch, 0) == 0
end

local function meet(p, q)  -- some string both globs match
  local memo = {}
  local function f(i, j)
    local k = i * 65536 + j
    if memo[k] == nil then
      local a, b = p[i], q[j]
      if not a and not b then memo[k] = true
      elseif a == "*" then memo[k] = f(i + 1, j) or (b ~= nil and f(i, j + 1))
      elseif b == "*" then memo[k] = f(i, j + 1) or (a ~= nil and f(i + 1, j))
      elseif not a or not b then memo[k] = false
      else memo[k] = one(a, b) and f(i + 1, j + 1) end
    end
    return memo[k]
  end
  return f(1, 1)
end

-- Whether some path is covered by both lock patterns (each as a glob, or as a directory: covers' two forms).
function M.overlaps(p, q)
  -- shortcut: a glob's directory form only covers names with a literal * ? or [ in them; left out
  local function forms(x) return x:find("[*?[]") and { tokens(x) } or { tokens(x), tokens(x, true) } end
  for _, x in ipairs(forms(p)) do
    for _, y in ipairs(forms(q)) do
      if meet(x, y) then return true end
    end
  end
  return false
end

-- A lock path as typed (absolute, ./x, or relative to a subdirectory) -> repo-relative, which is what the edit
-- hook matches. A trailing slash (a directory lock) is kept; outside a repo it stays as typed.
local function norm(path)
  local _, rel = M.repo_rel(path)
  if not rel then return path end
  return rel .. ((path:sub(-1) == "/" and rel ~= ".") and "/" or "")
end

function M.lock_holder(c, me_, path, t)
  for _, r in ipairs(c:all("select l.* from lock l join agent a on a.name=l.agent "
    .. "where l.agent!=? and l.lease_until>? and a.ended is null", me_, t)) do
    if M.covers(path, r.path) then return r end
  end
  return nil
end

function M.task_of(c, name)
  local r = c:one("select id,title from task where owner=? and state in ('claimed','blocked') order by id limit 1", name)
  return r and ("task #%d: %s"):format(r.id, r.title) or "no claimed task"
end

function M.cmd_lock(c, a)
  local n = agents.me()
  a.path = norm(a.path)
  c:tx(function()  -- scan and write in one transaction: a concurrent lock waits, then sees this one
    agents.touch(c, n)
    for _, o in ipairs(c:all("select l.* from lock l join agent g on g.name=l.agent where l.agent!=? and l.lease_until>? "
      .. "and g.ended is null", n, util.now())) do
      if M.overlaps(a.path, o.path) then
        util.die(("%s overlaps %s, locked by %s; message it"):format(a.path, o.path, o.agent))
      end
    end
    -- replaces only this agent's own lock (a renew) or a dead or expired one: a live peer's was refused above
    c:exec("insert or replace into lock(path,agent,reason,since,lease_until,seen) values(?,?,?,?,?,0)",
      a.path, n, a.reason, util.now(), util.now() + util.dur(a.lease))
    db.log(c, n, "lock", a.path, a.reason)
  end)
  print("locked " .. a.path)
end

function M.cmd_unlock(c, a)
  local n = agents.me()
  a.path = norm(a.path)
  c:exec("delete from lock where path=? and agent=?", a.path, n)
  db.log(c, n, "unlock", a.path)
  print("unlocked " .. a.path)
end

return M
