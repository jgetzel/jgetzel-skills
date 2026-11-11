-- This machine's processes and memory: the one seam that reads the system (sw-roles §6a). procs() is `ps` on Linux
-- and macOS; mem() and cwds() read /proc (SWARM_PROC in tests) on Linux and sysctl, vm_stat and lsof on macOS.
local util, json, db, re = require "swarm.util", require "swarm.json", require "swarm.db", require "swarm.re"
local proc = require "swarm.proc"
local unistd, lfs = require "posix.unistd", require "lfs"
local M = {}

M.PROC = os.getenv("SWARM_PROC") or "/proc"
M.OS = os.getenv("SWARM_OS") or require("posix.sys.utsname").uname().sysname  -- "Linux", "Darwin"; tests fake Linux

-- `ps` time ([[dd-]hh:]mm:ss[.cc], both systems' etime and time) in seconds.
function M.ps_secs(s)
  local dd, rest = s:match("^(%d+)%-(.*)$")
  local n = 0
  for x in (rest or s):gmatch("[^:]+") do n = n * 60 + (tonumber(x) or 0) end
  return math.floor(n + (tonumber(dd) or 0) * 86400)
end

-- `ps -o pid=,ppid=,rss=,etime=,time=,args=` text as {pid = {pid, ppid, rss_kb, age, cpu_s, args, argv, comm}}.
function M.parse_ps(txt)
  local out = {}
  for l in (txt or ""):gmatch("[^\n]+") do
    local pid, ppid, rss, et, tm, args = l:match("^%s*(%d+)%s+(%d+)%s+(%d+)%s+(%S+)%s+(%S+)%s?(.*)$")
    if pid then
      local argv = util.split(args)
      out[tonumber(pid)] = { pid = tonumber(pid), ppid = tonumber(ppid), rss_kb = tonumber(rss), age = M.ps_secs(et),
        cpu_s = M.ps_secs(tm), args = args, argv = argv, comm = util.basename(argv[1] or "") }
    end
  end
  return out
end

-- Every process, one `ps` (same columns in procps and BSD ps).
function M.procs()
  return M.parse_ps(proc.run({ "ps", "-axww", "-o", "pid=,ppid=,rss=,etime=,time=,args=" }, nil, nil, { LC_ALL = "C" }))
end

-- macOS readings to (avail_kb, total_kb, {level, load, cores}): `sysctl -n` hw.memsize, kern.memorystatus_vm_pressure_level
-- (1 normal, 2 warn, 4 critical), vm.loadavg ("{ 1.2 1.1 1.0 }"), hw.ncpu; and `vm_stat`.
function M.darwin_mem(memsize, vmstat, level, loadavg, ncpu)
  local total = tonumber(memsize or "")
  if not (total and vmstat) then return nil end
  local pg = tonumber(vmstat:match("page size of (%d+) bytes")) or 4096
  local pages = 0
  for _, k in ipairs({ "free", "inactive", "speculative", "purgeable" }) do
    pages = pages + (tonumber(vmstat:match("Pages " .. k .. ":%s+(%d+)")) or 0)
  end
  return math.floor(pages * pg / 1024), math.floor(total / 1024), { level = ({ "normal", "warn", nil, "critical" })[tonumber(level or "")],
    load = tonumber((loadavg or ""):match("[%d.]+")), cores = tonumber(ncpu or "") }
end

-- Memory available and total in KiB and a pressure reading: on Linux PSI {memory, cpu} some avg10, on macOS
-- {level, load, cores}. nil when unreadable.
function M.mem()
  if M.OS == "Darwin" then
    local function sc(k) return util.strip(proc.run({ "sysctl", "-n", k }) or "") end
    return M.darwin_mem(sc("hw.memsize"), proc.run({ "vm_stat" }), sc("kern.memorystatus_vm_pressure_level"),
      sc("vm.loadavg"), sc("hw.ncpu"))
  end
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

-- `lsof -Fpn` text as {pid = path}.
function M.parse_lsof(txt)
  local out, pid = {}, nil
  for l in (txt or ""):gmatch("[^\n]+") do
    local k, v = l:sub(1, 1), l:sub(2)
    if k == "p" then pid = tonumber(v) elseif k == "n" and pid then out[pid] = v end
  end
  return out
end

-- Each process's cwd as {pid = path}, or nil when no process's can be read (callers then assume every dir is in use).
function M.cwds()
  if M.OS == "Darwin" then  -- own processes need no sudo; others' are skipped with a warning on stderr
    local out = M.parse_lsof(proc.exec({ "lsof", "-a", "-d", "cwd", "-Fpn" }))
    return next(out) and out or nil
  end
  local ok, it, dir = pcall(lfs.dir, M.PROC)
  if not ok then return nil end
  local out = {}
  for e in it, dir do
    local l = e:match("^%d+$") and unistd.readlink(M.PROC .. "/" .. e .. "/cwd")
    if l then out[tonumber(e)] = l end
  end
  return out
end

M.CGROUP = os.getenv("SWARM_CGROUP") or "/sys/fs/cgroup"

-- The cgroup directory of the swarm-agent scope (relaunch/launch.sh) pid runs in, with its kernel-kept peak memory (KiB)
-- and CPU seconds; nil where there is none (no systemd user session, macOS, an unwrapped launch).
function M.cgroup(pid)
  local rel = (util.slurp(M.PROC .. "/" .. util.d(pid) .. "/cgroup") or ""):match("0::(/[^\n]*/swarm%-agent%-[^/\n]*%.scope)")
  local peak = rel and tonumber(util.slurp(M.CGROUP .. rel .. "/memory.peak") or "")
  if not peak then return nil end
  local usec = (util.slurp(M.CGROUP .. rel .. "/cpu.stat") or ""):match("usage_usec (%d+)")
  return { dir = M.CGROUP .. rel, peak_kb = math.floor(peak / 1024), cpu_s = math.floor((tonumber(usec) or 0) / 1e6) }
end

function M.pressure_high(avail, total, psi)
  if psi.level then return psi.level ~= "normal" end
  return (psi.memory or 0) > 10 or avail < 0.15 * total
end

function M.machine_line(avail, total, psi)
  if not avail then return "machine: unknown (memory unreadable)" end
  local mem = ("machine: %.1f/%.1fG mem available, "):format(avail / 1048576, total / 1048576)
  if not psi.memory then
    return mem .. ("pressure %s, load %s on %s cores"):format(psi.level or "unknown", psi.load or "?", psi.cores or "?")
  end
  return mem .. ("pressure10 mem %g%% cpu %g%%"):format(psi.memory, psi.cpu)
end

-- Nearest ancestor that is the claude process (its command's name contains 'claude').
function M.claude_pid(procs)
  procs = procs or M.procs()
  local p = procs[unistd.getppid()]
  for _ = 1, 64 do
    if not p or p.pid <= 1 then return nil end
    if p.comm:find("claude", 1, true) then return p.pid end
    p = procs[p.ppid]
  end
end

-- argv as 'tool arg ...' with path and interpreter stripped, so `node /x/tsc` reads as `tsc`.
function M.proc_cmd(p)
  local w = {}
  for i, x in ipairs(p.argv) do w[i] = i <= 2 and util.basename(x) or x end
  if #w > 1 and re.fullmatch([[(python[\d.]*|node|bash|sh)]], w[1]) then table.remove(w, 1) end
  return table.concat(w, " ")
end

-- Memory held per owner, by measurement: every process under a claude process, attributed to the agent whose claude it
-- is under (else "other session"). {agent, kb, top, top_kb, age, procs = {the tree's processes, its claude excluded}},
-- biggest first. No word picks which processes count.
function M.holders(c, procs)
  local owner = {}
  for _, r in ipairs(c:all("select name,claude_pid from agent where ended is null and claude_pid is not null")) do
    owner[r.claude_pid] = r.name
  end
  local by = {}
  for _, p in pairs(procs) do
    local q, who, hop = p, nil, 0
    while q and hop < 64 do
      who = owner[q.pid] or (q.comm:find("claude", 1, true) and "other session") or nil
      if who then break end
      q, hop = procs[q.ppid], hop + 1
    end
    if who then
      local h = by[who] or { agent = who, kb = 0, top_kb = -1, procs = {} }
      by[who] = h
      h.kb = h.kb + p.rss_kb
      if not owner[p.pid] then h.procs[#h.procs + 1] = p end
      if p.rss_kb > h.top_kb and not owner[p.pid] then h.top, h.top_kb, h.age = M.proc_cmd(p), p.rss_kb, p.age end
    end
  end
  local out = {}
  for _, h in pairs(by) do out[#out + 1] = h end
  table.sort(out, function(a, b)
    if a.kb ~= b.kb then return a.kb > b.kb end
    return a.agent < b.agent
  end)
  return out
end

-- Agents running a Bash-tool shell (it sources a shell snapshot; hooks such as the waiter don't) under their claude
-- process. An idle agent's foreground commands have ended, so for it this is a background job.
-- shortcut: a background subagent with no shell running isn't seen; add a signal if those lose claims too.
function M.bg_agents(c, procs)
  local owner, out = {}, {}
  for _, r in ipairs(c:all("select name,claude_pid from agent where ended is null and claude_pid is not null")) do
    owner[r.claude_pid] = r.name
  end
  for _, p in pairs(procs) do
    if owner[p.ppid] and p.args:find("/shell-snapshots/snapshot-", 1, true) then
      out[owner[p.ppid]] = true
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
      out[#out + 1] = ("%s: %.0f/%.0fG available, load %g on %d cores, mem pressure %s%s%s"):format(n,
        m.avail_kb / 1048576, m.total_kb / 1048576, m.load, m.cores, m.level or (("%g%%"):format(m.psi or 0)), old,
        #js > 0 and ", jobs: " .. table.concat(js, ", ") or "")
    end
  end
  return out
end

-- <= 6 lines: machine state, memory per owner by measurement (agents, then "other sessions") with its largest process;
-- then one line per other hc machine from watchd's cache.
function M.machine_note(c, me, procs)
  local avail, total, psi = M.mem()
  local hs = M.holders(c, procs or M.procs())
  local lines = { M.machine_line(avail, total, psi) }
  for i = 1, math.min(3, #hs) do
    local h = hs[i]
    lines[#lines + 1] = ("  %s %.1fG%s"):format(h.agent, h.kb / 1048576, h.top and (" (%s %.1fG)"):format(util.cut(h.top, 40), h.top_kb / 1048576) or "")
  end
  if #hs > 3 then lines[#lines + 1] = ("  +%d more holders"):format(#hs - 3) end
  for _, l in ipairs(M.remote_lines(c)) do lines[#lines + 1] = l end
  return table.concat(lines, "\n")
end

function M.cmd_machine(c)
  print(M.machine_note(c, nil))
end

return M
