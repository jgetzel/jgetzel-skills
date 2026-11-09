-- This machine's memory and pressure, from /proc (SWARM_PROC in tests). Linux only for now (sw-lua §8).
local util, json, db, re = require "swarm.util", require "swarm.json", require "swarm.db", require "swarm.re"
local proc = require "swarm.proc"
local unistd, lfs = require "posix.unistd", require "lfs"
local M = {}

M.PROC = os.getenv("SWARM_PROC") or "/proc"

-- MemAvailable and MemTotal in KiB and {memory, cpu} PSI some avg10, or nil without /proc/meminfo.
function M.mem_psi()
  local s = util.slurp(M.PROC .. "/meminfo")
  if not s then return nil end
  local mi = {}
  for k, v in s:gmatch("([^\n:]+):%s*(%d+)") do mi[k] = tonumber(v) end
  local psi = {}
  for _, r in ipairs({ "memory", "cpu" }) do
    psi[r] = tonumber((util.slurp(M.PROC .. "/pressure/" .. r) or ""):match("some avg10=([%d.]+)")) or 0
  end
  return mi.MemAvailable, mi.MemTotal, psi
end

function M.pressure_high(avail, total, psi)
  return psi.memory > 10 or avail < 0.15 * total
end

function M.machine_line(avail, total, psi)
  if not avail then return "machine: unknown (no /proc here)" end
  return ("machine: %.1f/%.1fG mem available, pressure10 mem %g%% cpu %g%%"):format(
    avail / 1048576, total / 1048576, psi.memory, psi.cpu)
end

M.HEAVY_RE = [[\b(cabal|stack|ghc|make|cmake|ninja|gradle|mvn|pytest|tox|tsc|spago|purs|playwright|nix\s+(build|flake\s+check)|docker\s+build|(cargo|go|npm|pnpm|yarn|bun)\s+(run\s+)?(build|test|check|clippy|bench|install))\b]]
M.NOT_HEAVY = [[\s*(git|gh|swarm|echo|grep|rg|cat|ls|sed|head|tail)\b]]  -- shortcut: first-word skip so `git commit -m make` isn't flagged

-- Does a Bash command look like a build/test (built-in words plus the repo's .claude/swarm.json {"heavy": [regex]})?
function M.is_heavy(cmd, cwd)
  if re.match([[\s*swarm\s+run\b]], cmd) then return true end
  if re.match(M.NOT_HEAVY, cmd) then return false end
  if re.search(M.HEAVY_RE, cmd) then return true end
  local top = proc.git({ "rev-parse", "--show-toplevel" }, cwd)
  local j = top and json.decode(util.slurp(util.join(top, ".claude", "swarm.json")) or "")
  for _, x in ipairs(type(j) == "table" and type(j.heavy) == "table" and j.heavy or {}) do
    local ok, m = pcall(re.search, x, cmd)
    if ok and m then return true end
  end
  return false
end

-- Nearest ancestor that is the claude process (its comm contains 'claude').
function M.claude_pid()
  local pid = unistd.getppid()
  while pid > 1 do
    local comm, st = util.slurp("/proc/" .. pid .. "/comm"), util.slurp("/proc/" .. pid .. "/stat")
    if not (comm and st) then return nil end
    if comm:find("claude", 1, true) then return pid end
    pid = tonumber(st:match("^.*%)%s+%S+%s+(%d+)"))
    if not pid then return nil end
  end
end

-- One /proc scan: {pid = {pid, ppid, comm, rss_kb, age, argv, cwd}}.
function M.read_procs()
  local up = tonumber((util.slurp(M.PROC .. "/uptime") or ""):match("^%S+")) or 0
  local tck, pg = unistd.sysconf(unistd._SC_CLK_TCK), unistd.sysconf(unistd._SC_PAGESIZE) / 1024
  local out = {}
  local ok, it, dir = pcall(lfs.dir, M.PROC)
  if not ok then return out end
  for d in it, dir do
    local st = d:match("^%d+$") and util.slurp(M.PROC .. "/" .. d .. "/stat")
    local cl = st and util.slurp(M.PROC .. "/" .. d .. "/cmdline")
    local a, b = st and st:find("(", 1, true), st and st:match("^.*()%)")
    if a and b then
      local rest = util.split(st:sub(b + 2))
      if cl and tonumber(rest[22]) then
        local argv = {}
        for x in cl:gmatch("[^%z]+") do argv[#argv + 1] = x end
        out[tonumber(d)] = { pid = tonumber(d), ppid = tonumber(rest[2]), comm = st:sub(a + 1, b - 1),
          rss_kb = tonumber(rest[22]) * pg, age = math.max(0, up - tonumber(rest[20]) / tck), argv = argv }
      end
    end
  end
  return out
end

-- argv as 'tool arg ...' with path and interpreter stripped, so `node /x/tsc` reads as `tsc`.
function M.proc_cmd(p)
  local w = {}
  for i, x in ipairs(p.argv) do w[i] = i <= 2 and util.basename(x) or x end
  if #w > 1 and re.fullmatch([[(python[\d.]*|node|bash|sh)]], w[1]) then table.remove(w, 1) end
  return table.concat(w, " ")
end

-- Heavy processes with the swarm agent each belongs to (walk ppid up to an agent's claude pid), else 'other session'.
function M.heavy_procs(c, procs)
  local owner = {}
  for _, r in ipairs(c:all("select name,claude_pid from agent where ended is null and claude_pid is not null")) do
    owner[r.claude_pid] = r.name
  end
  local out = {}
  for _, p in pairs(procs) do
    local cmd = M.proc_cmd(p)
    if re.match(M.HEAVY_RE, cmd) or re.match([[ghc(-[\d.]+)?\b]], cmd) then
      local q, who, hop = p, "other session", 0
      while q and hop < 64 do
        if owner[q.pid] then who = owner[q.pid]; break end
        q, hop = procs[q.ppid], hop + 1
      end
      out[#out + 1] = { pid = p.pid, ppid = p.ppid, comm = p.comm, rss_kb = p.rss_kb, age = p.age, cmd = cmd, agent = who }
    end
  end
  return out
end

-- job-start events with no job-end yet, newest first, data unpacked.
function M.live_jobs(c, t)
  local ended, out = {}, {}
  for _, r in ipairs(c:all("select path from event where kind='job-end'")) do ended[r.path] = true end
  for _, r in ipairs(c:all("select ts,agent,path,data from event where kind='job-start' and ts>? order by id desc",
      (t or util.now()) - 86400)) do
    local j = not ended[r.path] and json.decode(r.data or "{}")
    if type(j) == "table" then
      j.ts, j.agent, j.id = r.ts, r.agent, r.path
      out[#out + 1] = j
    end
  end
  return out
end

-- One line per other machine from watchd's cache (the hook never waits on the network), with this repo's live jobs on it.
function M.remote_lines(c, t)
  t = t or util.now()
  local r = c:one("select v from meta where k='machines'")
  local ms = r and json.decode(r.v)
  if type(ms) ~= "table" then return {} end
  local jobs, names, out = M.live_jobs(c, t), {}, {}
  for n in pairs(ms) do names[#names + 1] = n end
  table.sort(names)
  for _, n in ipairs(names) do
    local m, js = ms[n], {}
    for _, j in ipairs(jobs) do
      local rd = j.machine == n and type(m.jobs) == "table" and m.jobs[j.id]
      if j.machine == n then
        js[#js + 1] = ("%s %s %s"):format(j.agent, util.cut(j.cmd or "", 24), util.ago(j.ts))
          .. (type(rd) == "table" and rd.rss_kb and (" %.1fG"):format(rd.rss_kb / 1048576) or "")
      end
    end
    if m.state ~= "connected" then
      out[#out + 1] = ("%s: %s since %s"):format(n, m.state, util.hhmm(m.since or m.ts))
    else
      local old = t - m.ts > 120 and (" (as of %s ago)"):format(util.ago(m.ts)) or ""
      out[#out + 1] = ("%s: %.0f/%.0fG available, load %g on %d cores, mem pressure %g%%%s%s"):format(n,
        m.avail_kb / 1048576, m.total_kb / 1048576, m.load, m.cores, m.psi, old,
        #js > 0 and ", jobs: " .. table.concat(js, ", ") or "")
    end
  end
  return out
end

-- <= 6 lines: machine state, running heavy processes (attributed), builds other agents started in the last minute;
-- then one line per other hc machine from watchd's cache.
function M.machine_note(c, me, procs)
  local avail, total, psi = M.mem_psi()
  local hv = M.heavy_procs(c, procs or M.read_procs())
  table.sort(hv, function(a, b) return a.rss_kb ~= b.rss_kb and a.rss_kb > b.rss_kb or a.pid < b.pid end)
  local lines = { M.machine_line(avail, total, psi) }
  for i = 1, math.min(3, #hv) do
    local h = hv[i]
    lines[#lines + 1] = ("  running: %s %.1fG %dm (%s)"):format(util.cut(h.cmd, 40), h.rss_kb / 1048576,
      math.floor(h.age / 60), h.agent)
  end
  if #hv > 3 then lines[#lines + 1] = ("  +%d more heavy processes"):format(#hv - 3) end
  local st, t = {}, util.now()
  for _, e in ipairs(c:all("select * from event where kind='heavy-start' and ts>? and agent!=? order by ts", t - 60, me or "")) do
    st[#st + 1] = ("%s: %s (%ds ago)"):format(e.agent, util.cut(e.data or "", 30), t - e.ts)
  end
  if #st > 0 then lines[#lines + 1] = "  started in the last 60s: " .. table.concat(st, "; ", 1, math.min(3, #st)) end
  for _, l in ipairs(M.remote_lines(c)) do lines[#lines + 1] = l end
  return table.concat(lines, "\n")
end

function M.cmd_machine(c)
  print(M.machine_note(c, nil))
end

return M
