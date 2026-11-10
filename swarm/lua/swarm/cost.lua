-- The cmd-cost history (sw-roles §6a): one row per finished command that cost something, measured on watchd's tick from
-- the Bash-tool shells under claude processes. The file is per user and machine, outside swarm.db; schema: cmd-cost.md.
local util, db, json, proc = require "swarm.util", require "swarm.db", require "swarm.json", require "swarm.proc"
local machine = require "swarm.machine"
local unistd = require "posix.unistd"
local M = {}

M.KEEP = 20          -- rows per (machine, repo, key)
M.MIN_WALL = 60      -- a command is recorded when it ran this long (s) ...
M.MIN_PEAK_KB = 1048576  -- ... or peaked this high (1 GiB)

M.SCHEMA = [[
create table if not exists cmd(id integer primary key, ts int, machine text, repo text, agent text, source text,
  cmd text, key text, wall_s int, cpu_s int, peak_kb int, exact int);
create index if not exists cmd_key on cmd(machine, repo, key, id);
]]

function M.path()
  local x = os.getenv("XDG_STATE_HOME")
  if not x or x == "" then x = (os.getenv("HOME") or "") .. "/.local/state" end
  return x .. "/cmd-cost/history.db"
end

function M.open() return db.open_at(M.path(), M.SCHEMA) end

local cached  -- watchd's long-lived connection, reopened if the path moved
function M.handle()
  if not (cached and cached.path == M.path()) then cached = M.open() end
  return cached
end

-- The command with a leading `cd … &&`, `swarm run … --`, environment assignments and trailing pipes and
-- redirections stripped, cut to its first three words.
-- shortcut: crude (three words can merge a one-crate test with a workspace test); the full cmd is kept to recompute.
function M.key(cmd)
  local s = util.strip(cmd or "")
  repeat
    local n = #s
    s = s:gsub("^cd%s+[^&;]+&&%s*", ""):gsub("^swarm%s+run%s.-%s%-%-%s+", ""):gsub("^[%a_][%w_]*=%S*%s+", "")
  until #s == n
  s = s:gsub("%s*|.*$", ""):gsub("%s+%d*[<>].*$", "")
  local w = util.split(s)
  return table.concat(w, " ", 1, math.min(3, #w))
end

-- The command a Bash-tool shell was asked to run: `eval '<cmd>' \< /dev/null && pwd -P >| …`.
function M.shell_cmd(args)
  local body = args:match("eval%s+(.-)%s+\\<%s+/dev/null") or args:match("eval%s+(.*)$")
  if not body then return nil end
  return (body:gsub("^'", ""):gsub("'$", ""):gsub("'\\''", "'"))
end

function M.hostname() return require("posix.sys.utsname").uname().nodename end

function M.record(h, r)
  if not (r.wall_s >= M.MIN_WALL or r.peak_kb >= M.MIN_PEAK_KB) then return false end
  r.key = r.key or M.key(r.cmd)
  h:exec("insert into cmd(ts,machine,repo,agent,source,cmd,key,wall_s,cpu_s,peak_kb,exact) values(?,?,?,?,?,?,?,?,?,?,?)",
    r.ts or util.now(), r.machine or M.hostname(), r.repo, r.agent, r.source or "swarm", r.cmd, r.key, r.wall_s, r.cpu_s or 0,
    r.peak_kb, r.exact or 0)
  h:exec("delete from cmd where machine=? and repo=? and key=? and id not in (select id from cmd where machine=? and repo=? "
    .. "and key=? order by id desc limit ?)", r.machine or M.hostname(), r.repo, r.key, r.machine or M.hostname(), r.repo,
    r.key, M.KEEP)
  return true
end

-- The repo's name (its main checkout's directory) and every worktree path.
local function repo_info()
  local common = proc.git({ "rev-parse", "--path-format=absolute", "--git-common-dir" })
  if not common or common == "" then return nil end
  local wts = {}
  for l in (proc.git({ "worktree", "list", "--porcelain" }) or ""):gmatch("[^\n]+") do
    wts[#wts + 1] = l:match("^worktree (.+)$") or nil
  end
  return util.basename(util.dirname(common)), wts
end

local function inside(p, dirs)
  for _, w in ipairs(dirs) do
    if p == w or util.startswith(p, w .. "/") then return true end
  end
end

local function clk() return unistd.sysconf and unistd.sysconf(unistd._SC_CLK_TCK) or 100 end

-- Seconds of CPU the shell's reaped children used (Linux); 0 where /proc has no such file.
local function reaped_cpu(pid)
  local s = util.slurp(machine.PROC .. "/" .. util.d(pid) .. "/stat")
  local rest = s and s:match("^.*%)%s+(.*)$")
  if not rest then return 0 end
  local f = util.split(rest)
  return ((tonumber(f[14]) or 0) + (tonumber(f[15]) or 0)) / clk()
end

M.open_cmds = {}  -- shell pid -> {agent, cmd, wall, peak, cpu, repo}: a watchd restart forgets them

-- One watchd tick: update the table of live command shells, and write a row for each that is gone.
-- procs: machine.procs(); t: now. User sessions (claude processes of no agent) count when their cwd is in this repo.
function M.tick(c, h, procs, t)
  local owner = {}
  for _, r in ipairs(c:all("select name,claude_pid from agent where ended is null and claude_pid is not null")) do
    owner[r.claude_pid] = r.name
  end
  local kids, shells = {}, {}
  for _, p in pairs(procs) do
    kids[p.ppid] = kids[p.ppid] or {}
    table.insert(kids[p.ppid], p)
    if p.args:find("/shell-snapshots/snapshot-", 1, true) then shells[#shells + 1] = p end
  end
  local repo, wts, cw
  local seen = {}
  for _, sh in ipairs(shells) do
    local par = procs[sh.ppid]
    local who = owner[sh.ppid]
    if not who and par and par.comm:find("claude", 1, true) then  -- someone's own session: ours only if its cwd is in this repo
      if not repo then repo, wts = repo_info() end
      cw = cw or machine.cwds() or {}
      if repo and cw[par.pid] and inside(cw[par.pid], wts) then
        who = "user:" .. (par.args:match("%s%-n%s+(%S+)") or par.args:match("%s%-%-name[ =](%S+)") or ""):gsub(":$", "")
        if who == "user:" then who = "user" end
      end
    end
    if who then
      local rss, cpu, q, i = 0, 0, { sh }, 1
      while q[i] do
        rss, cpu = rss + q[i].rss_kb, cpu + q[i].cpu_s
        for _, k in ipairs(kids[q[i].pid] or {}) do q[#q + 1] = k end
        i = i + 1
      end
      local o = M.open_cmds[sh.pid]
      if o and sh.age < o.wall then o = nil end  -- the pid was reused
      if not o then
        o = { agent = who, cmd = M.shell_cmd(sh.args) or "?", wall = 0, peak = 0, cpu = 0 }
        M.open_cmds[sh.pid] = o
      end
      o.wall, o.peak = sh.age, math.max(o.peak, rss)
      o.cpu = math.max(o.cpu, cpu, reaped_cpu(sh.pid))
      seen[sh.pid] = true
    end
  end
  for pid, o in pairs(M.open_cmds) do
    if not seen[pid] then
      M.open_cmds[pid] = nil
      repo = repo or repo_info()
      M.record(h, { ts = t, repo = repo or "?", agent = o.agent, cmd = o.cmd, wall_s = o.wall, cpu_s = math.floor(o.cpu),
        peak_kb = o.peak })
    end
  end
end

local function median(a)
  table.sort(a)
  return a[math.floor((#a + 1) / 2)] or 0
end

local function mins(s) return ("%d min"):format(math.max(1, math.floor(s / 60 + 0.5))) end
local function gib(kb) return ("%.1fG"):format(kb / 1048576) end

-- "`cargo test`, this repo, this machine: 5 runs, median 6 min, peak 9.4G (max 11.2G), 31 CPU-min." or nil.
function M.summary(h, repo, key)
  local rows = h:all("select wall_s,cpu_s,peak_kb from cmd where machine=? and repo=? and key=?", M.hostname(), repo, key)
  if #rows == 0 then return nil end
  local w, cp, pk, mx = {}, {}, {}, 0
  for i, r in ipairs(rows) do
    w[i], cp[i], pk[i], mx = r.wall_s, r.cpu_s, r.peak_kb, math.max(mx, r.peak_kb)
  end
  return ("`%s`, this repo, this machine: %d run%s, median %s, peak %s (max %s), %d CPU-min."):format(key, #rows,
    #rows == 1 and "" or "s", mins(median(w)), gib(median(pk)), gib(mx), math.floor(median(cp) / 60 + 0.5))
end

function M.cmd_cost(_, a)
  if not unistd.access(M.path(), "r") then print("no history yet (watchd records commands that run a minute or take 1G)"); return end
  local h = M.open()
  local repo = a.repo or (repo_info())
  if a.top then
    local where, args = "where machine=?", { M.hostname() }
    if not a.all_repos then where = where .. " and repo=?"; args[2] = repo end
    for _, by in ipairs({ { "peak_kb", "peak" }, { "cpu_s", "cpu" } }) do
      print("by " .. by[2] .. ":")
      for _, r in ipairs(h:all(("select repo,key,count(*) n,max(peak_kb) peak,max(cpu_s) cpu,max(wall_s) wall from cmd %s group by repo,key "
          .. "order by max(%s) desc limit 5"):format(where, by[1]), table.unpack(args))) do
        print(("  %s%s: %d run%s, peak %s, %s, %d CPU-min"):format(a.all_repos and r.repo .. " " or "", r.key, r.n,
          r.n == 1 and "" or "s", gib(r.peak), mins(r.wall), math.floor(r.cpu / 60 + 0.5)))
      end
    end
    return
  end
  if #a.words == 0 then util.die("swarm cost \"<command>\" or swarm cost --top") end
  local key = M.key(table.concat(a.words, " "))
  print(M.summary(h, repo, key) or ("no history for `" .. key .. "` here"))
end

return M
