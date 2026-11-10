-- swarm run: a build or test here, or on another hc machine against a copy of this worktree, recorded as a job.
local util, proc, json, re = require "swarm.util", require "swarm.proc", require "swarm.json", require "swarm.re"
local db, machine = require "swarm.db", require "swarm.machine"
local lfs, stdlib = require "lfs", require "posix.stdlib"
local utf8 = require "lua-utf8"
local M = {}

M.RUN_DIR = ".cache/swarm-run"  -- under each machine's home: <repo>/<worktree>/{src,jobs/<id>}, plus whatever `set` puts in {dir}
local JOB_TAIL = 200

-- {name: {state, target, ...}} from `hc machine ls`, {} without hc.
function M.hc_machines()
  local ok, d = pcall(json.decode, proc.run({ "hc", "machine", "ls", "--json" }) or "{}")
  local r = {}
  if ok and type(d) == "table" and type(d.machines) == "table" then
    for _, m in ipairs(d.machines) do
      if type(m) == "table" and m.name then r[m.name] = m end
    end
  end
  return r
end

-- job-start events with no job-end yet, newest first, data unpacked.
function M.live_jobs(c, t)
  local ended = {}
  for _, r in ipairs(c:all("select path from event where kind='job-end'")) do ended[r.path] = true end
  local out = {}
  for _, r in ipairs(c:all("select ts,agent,path,data from event where kind='job-start' and ts>? order by id desc",
      (t or util.now()) - 86400)) do
    if not ended[r.path] then
      local ok, j = pcall(json.decode, r.data or "{}")
      if ok and type(j) == "table" then
        j.ts, j.agent, j.id = r.ts, r.agent, r.path
        out[#out + 1] = j
      end
    end
  end
  return out
end

function M.pid_alive(pid)
  pid = tonumber(pid)
  return pid ~= nil and require("posix.signal").kill(pid, 0) == 0
end

M.LOST_FOR = 3600  -- a job whose terminal is gone this long gets a job-end 'lost', so Running now drops it

-- Load and memory, then (with job terminals as args) every process and each terminal's `hc get`; ps flags work on Linux and macOS.
local PROBE = "if [ \"$(uname)\" = Darwin ]; then echo @darwin; for k in hw.ncpu hw.memsize kern.memorystatus_vm_pressure_level "
  .. "vm.loadavg; do sysctl -n $k 2>/dev/null || echo; done; vm_stat; "
  .. "else nproc; cat /proc/loadavg /proc/meminfo; cat /proc/pressure/memory 2>/dev/null; fi; [ $# -gt 0 ] || exit 0; "
  .. "echo @ps; LC_ALL=C ps -Ao pid=,ppid=,rss=,pcpu=; "
  .. "for t; do echo \"@hc $t\"; hc get \"$t\" --json 2>&1 | tr -d '\\n'; echo; done"

-- RSS (KiB) and %CPU summed over root and its descendants. shortcut: %CPU is ps's (lifetime average on Linux).
local function tree_sum(ps, kids, root)
  local rss, cpu, q, i = 0, 0, { root }, 1
  while q[i] do
    local p = ps[q[i]]
    if p then rss, cpu = rss + p.rss, cpu + p.cpu end
    for _, k in ipairs(kids[q[i]] or {}) do q[#q + 1] = k end
    i = i + 1
  end
  return rss, cpu
end

-- {rss_kb, cpu} per live job, {gone = since} where the machine says its terminal is gone or ended.
local function job_readings(c, t, txt, mine, old)
  local ps, kids, got, cur = {}, {}, {}, nil
  for _, l in ipairs(util.splitlines(txt:match("\n@ps\n(.*)$") or "")) do
    local a = l:match("^@hc (%S+)$")
    if a then cur = a; got[a] = ""
    elseif cur then got[cur] = l
    else
      local pid, ppid, rss, cpu = l:match("^%s*(%d+)%s+(%d+)%s+(%d+)%s+([%d.]+)")
      if pid then
        pid, ppid = tonumber(pid), tonumber(ppid)
        ps[pid] = { rss = tonumber(rss), cpu = tonumber(cpu) }
        if pid ~= ppid then kids[ppid] = kids[ppid] or {}; table.insert(kids[ppid], pid) end
      end
    end
  end
  local out = {}
  for _, j in ipairs(mine) do
    local ok, g = pcall(json.decode, got[j.term] or "")
    g = ok and type(g) == "table" and g or {}
    if g.state == "live" and tonumber(g.pid) then
      local rss, cpu = tree_sum(ps, kids, tonumber(g.pid))
      out[j.id] = { rss_kb = rss, cpu = math.floor(cpu + 0.5) }
    elseif g.state or (type(g.error) == "table" and g.error.kind == "not_found") then  -- the machine answered: no such live terminal
      local since = type(old[j.id]) == "table" and old[j.id].gone or t
      out[j.id] = { gone = since }
      if t - since >= M.LOST_FOR and not M.pid_alive(j.pid) then
        db.log(c, j.agent, "job-end", j.id, json.encode({ machine = j.machine, exit = "lost", s = t - j.ts }))
      end
    end
  end
  return out
end

-- PROBE's head (before @ps) as {cores, load, avail_kb, total_kb, psi (Linux) or level (macOS)}, or nil.
function M.parse_probe(head)
  local l = util.splitlines(head)
  if l[1] == "@darwin" then
    local avail, total, p = machine.darwin_mem(l[3], table.concat(l, "\n", 6), l[4], l[5], l[2])
    if not (avail and p.cores and p.load) then return nil end
    return { cores = p.cores, load = p.load, avail_kb = avail, total_kb = total, level = p.level or "unknown" }
  end
  local cores, load = tonumber(l[1] or ""), tonumber((l[2] or ""):match("^%S+") or "")
  local avail, total = tonumber(head:match("MemAvailable:%s+(%d+)") or ""), tonumber(head:match("MemTotal:%s+(%d+)") or "")
  if not (cores and load and avail and total) then return nil end
  return { cores = cores, load = load, avail_kb = avail, total_kb = total, psi = tonumber(head:match("some avg10=([%d.]+)") or "") or 0 }
end

-- Each hc machine's load and memory and its jobs' process trees, one `hc exec` each, stored in meta 'machines'.
function M.remote_tick(c, t)
  local term = os.getenv("HC_TERMINAL_ID")
  if not term or term == "" then return end  -- only watchd started from a Herdr terminal probes; tests and plain shells skip it
  local ms = M.hc_machines()
  local r = c:one("select v from meta where k='machines'")
  local old = r and json.decode(r.v) or {}
  local names = {}
  for n in pairs(ms) do names[#names + 1] = n end
  table.sort(names)
  local jobs, out = M.live_jobs(c, t), {}
  for _, n in ipairs(names) do
    local m, o = ms[n], type(old[n]) == "table" and old[n] or {}
    local mine, cmd = {}, { "hc", "exec", "--on", n, "--timeout", "10", "sh", "-c", PROBE, "sh" }
    for _, j in ipairs(jobs) do
      if j.machine == n and type(j.hc) == "string" then
        j.term = j.hc:match("^[^/]*/(.+)$") or j.hc  -- "laptop/t12" is t12 there
        mine[#mine + 1] = j
        cmd[#cmd + 1] = j.term
      end
    end
    local txt = m.state == "connected" and proc.run(cmd) or nil
    local r = txt and M.parse_probe(txt:match("^(.-)\n@ps\n") or txt)
    if r then
      r.state, r.ts, r.jobs = "connected", t, job_readings(c, t, txt, mine, type(o.jobs) == "table" and o.jobs or {})
      out[n] = r
    else
      local st = m.state ~= "connected" and m.state or "unreachable"
      out[n] = { state = st, ts = t, since = o.state == st and o.since or t }
    end
  end
  c:exec("insert or replace into meta(k,v) values('machines',?)", json.encode(out))
end

-- Remove a landed worktree's dirs on every machine its jobs ran on.
function M.clean_remote(c, wt)
  local seen = {}
  for _, e in ipairs(c:all("select data from event where kind='job-start'")) do
    local j = json.decode(e.data or "{}")
    if type(j) == "table" and type(j.machine) == "string" and j.machine ~= "" and j.wt == wt and type(j.dir) == "string"
        and re.fullmatch(re.escape(M.RUN_DIR) .. [[/[\w.-]+/[\w.-]+]], j.dir) and not seen[j.machine .. "\0" .. j.dir] then
      seen[j.machine .. "\0" .. j.dir] = true
      local ok = proc.run({ "hc", "exec", "--on", j.machine, "--timeout", "120", "rm", "-rf", j.dir }) ~= nil
      db.log(c, nil, "remote-clean", j.dir, j.machine .. " " .. (ok and "ok" or "failed"))
    end
  end
end

-- ssh with one shared connection per host (each call after the first costs ~0.05 s) that gives up fast on a sleeping host.
function M.ssh_cmd()
  local cp = (os.getenv("TMPDIR") or "/tmp") .. "/swarm-ssh-%C"
  return { "ssh", "-o", "BatchMode=yes", "-o", "ConnectTimeout=5", "-o", "ServerAliveInterval=5", "-o",
    "ServerAliveCountMax=3", "-o", "ControlMaster=auto", "-o", "ControlPath=" .. cp, "-o", "ControlPersist=120" }
end

-- Names (no value) found by `env_scan` [glob, regex] pairs in files under top.
local function scan_names(cfg, top)
  local names = {}
  for _, ps in ipairs(cfg.env_scan or {}) do
    local out = proc.exec({ "sh", "-c", 'IFS=; for f in $1; do [ -f "$f" ] && printf "%s\\0" "$f"; done', "sh", ps[1] },
      { cwd = top })
    for _, f in ipairs(util.split(out, "\0")) do
      local s = f ~= "" and util.slurp(util.join(top, f))
      if s then
        for _, n in ipairs(re.findall(ps[2], (utf8.clean(s, "")))) do names[n] = true end
      end
    end
  end
  return names
end

-- Variables the job gets: names matching a `run.env` regex, names `run.env_scan` finds in files, and --env.
function M.job_env(cfg, top, extra)
  local names, env = scan_names(cfg, top), {}
  for k, v in pairs(stdlib.getenv()) do
    local hit = names[k]
    for _, p in ipairs(cfg.env or {}) do hit = hit or re.search(p, k) end
    if hit then env[k] = v end
  end
  for _, e in ipairs(extra or {}) do
    local k, v = e:match("^([^=]*)=(.*)$")
    if k then env[k] = v
    elseif stdlib.getenv(e) then env[e] = stdlib.getenv(e) end
  end
  return env
end

-- Tree of the working state (tracked + untracked, not ignored), written into a copy of the index; reads wt only.
local function tree_of(wt)
  local idx = proc.git({ "-C", wt, "rev-parse", "--path-format=absolute", "--git-path", "index" })
  if not (idx and proc.git({ "-C", wt, "rev-parse", "HEAD" })) then return nil end
  local tmp = os.tmpname()
  proc.exec({ "cp", "-p", idx, tmp })  -- keeps the index mtime, or git trusts stale stat data (racy git)
  local env = { GIT_INDEX_FILE = tmp, GIT_OPTIONAL_LOCKS = "0" }
  proc.exec({ "git", "-C", wt, "add", "-A" }, { env = env })
  local out = proc.exec({ "git", "-C", wt, "write-tree" }, { env = env })
  os.remove(tmp)
  out = util.strip(out)
  return out ~= "" and out or nil
end

-- {file: blob hash} for the plain files in list (one git call); used to tell "untouched here since the sync".
local function hashes(top, files)
  local names, h = {}, {}
  for _, f in ipairs(files) do
    local a = lfs.symlinkattributes(util.join(top, f))
    if a and a.mode == "file" and not f:find("\n", 1, true) then names[#names + 1] = f end
  end
  local out = proc.exec({ "git", "-C", top, "hash-object", "--stdin-paths" }, { input = table.concat(names, "\n") .. "\n" })
  for i, x in ipairs(util.splitlines(out)) do h[names[i]] = x end
  return h
end

local function exists(p)
  return lfs.symlinkattributes(p) ~= nil
end

local function mkdirp(d)
  proc.exec({ "mkdir", "-p", d })
end

local function sanitize(s)
  return (s:gsub("[^%w_.-]", "_"))
end

local function read_cfg(top)
  local s = util.slurp(util.join(top, ".claude", "swarm.json"))
  local ok, d = pcall(json.decode, s or "")
  local cfg = ok and type(d) == "table" and d.run
  return type(cfg) == "table" and cfg or {}
end

function M.cmd_run(c, a)
  local argv = a.argv or {}
  if #argv == 0 then util.die("usage: swarm run [--on <machine>] [--env NAME[=VAL]]... -- <cmd…>") end
  local top = proc.git({ "rev-parse", "--show-toplevel" })
  if not top or top == "" then util.die("not in a git repo") end
  top = stdlib.realpath(top)
  local common = proc.git({ "rev-parse", "--path-format=absolute", "--git-common-dir" })
  local repo = sanitize(common:sub(-5) == "/.git" and util.basename(util.dirname(common)) or util.basename(top))
  local wtname = sanitize(util.basename(top))
  local cwd = stdlib.realpath(lfs.currentdir())
  local rel = cwd == top and "." or (util.startswith(cwd, top .. "/") and cwd:sub(#top + 2) or ".")
  local cfg = read_cfg(top)
  local who = os.getenv("SWARM_NAME")
  if not who or who == "" then who = "human" end
  local line = #argv == 1 and argv[1] or util.shjoin(argv)  -- one argument is shell text
  local full = line
  if cfg.prefix then  -- the wrapper runs the whole command
    full = cfg.prefix .. " " .. (#argv == 1 and "sh -c " .. util.shquote(line) or line)
  end
  local env = M.job_env(cfg, top, a.env)
  local jid = util.d(tonumber(c:one("insert into meta(k,v) values('jobs','1') on conflict(k) do update set "
    .. "v=cast(v as int)+1 returning v").v))
  local jobs = util.join(util.dirname(db.dbpath()), "jobs", jid)
  mkdirp(jobs)
  local logf = jobs .. "/log"
  local task = c:one("select id from task where owner=? and state in ('claimed','blocked') order by id limit 1", who)
  local d = ("%s/%s/%s"):format(M.RUN_DIR, repo, wtname)
  local rec = { machine = a.on, wt = top, dir = d, task = task and task.id, cmd = full, pid = require("posix.unistd").getpid() }
  local clock = require("posix.time").clock_gettime
  local function now() local s = clock(require("posix.time").CLOCK_REALTIME or 0); return s.tv_sec + s.tv_nsec / 1e9 end
  local t0 = now()

  local function finish(code, tree, sync, back, kept)
    local s = math.floor(now() - t0)
    db.log(c, who, "job-end", jid, json.encode({ machine = a.on, exit = code, s = s, sync_s = sync, back_s = back, tree = tree }))
    local lines = util.splitlines(util.slurp(logf) or "")
    local tail = {}
    for i = math.max(1, #lines - JOB_TAIL + 1), #lines do tail[#tail + 1] = lines[i] end
    if #tail > 0 then print(table.concat(tail, "\n")) end
    local lost = code == "lost"
    print(("job j%s %s on %s, %dm%02ds"):format(jid, lost and "lost" or "exit " .. code, a.on or "this machine", math.floor(s / 60), s % 60)
      .. ((sync and back) and (" (sync %.1fs, back %.1fs)"):format(sync, back) or "")
      .. (tree and ", tree " .. tree:sub(1, 7) or "") .. "; log: " .. logf
      .. ((kept and #kept > 0) and ("\nkept your local edits; the job's versions of %s are in %s/kept/"):format(
        table.concat(kept, ", "), jobs) or "")
      .. ((lost and rec.hc) and ("\nthe terminal %s may still be running: `hc wait %s` later"):format(rec.hc, rec.hc) or ""))
    io.stdout:flush()
    util.exit(lost and 255 or code)
  end

  if not a.on then
    rec.dir = nil
    db.log(c, who, "job-start", jid, json.encode(rec))
    local tree = tree_of(top)
    local _, _, rc = proc.exec({ "sh", "-c", full }, { env = env, stdout_file = logf })
    return finish(rc >= 0 and rc or 128 - rc, tree)
  end

  local m = M.hc_machines()[a.on]
  if not m or m.state ~= "connected" then
    util.die(("machine %s is %s; the job never ran. Pick another (see the machine note)."):format(
      a.on, m and tostring(m.state) or "not in `hc machine ls`"), 255)
  end
  local ssh = util.shjoin(M.ssh_cmd())
  local tgt = m.target
  local busy = 0
  for _, j in ipairs(M.live_jobs(c)) do
    if j.machine == a.on and j.wt == top and M.pid_alive(j.pid) then busy = busy + 1 end
  end
  local src = d .. "/src" .. (busy > 0 and "." .. (busy + 1) or "")  -- a second job from this worktree gets its own copy, sharing {dir}
  local files = {}  -- local files as they are now, to keep edits made while the job ran
  for _, f in ipairs(util.split(proc.run({ "git", "-C", top, "ls-files", "-z", "-c", "-o", "--exclude-standard" }) or "", "\0")) do
    if f ~= "" then files[#files + 1] = f end
  end
  local before = hashes(top, files)
  local _, rerr, rrc = proc.exec({ "rsync", "-rlpD", "--checksum", "--delete", "--exclude=.git", "--filter=:- .gitignore",
    "--mkpath", "-e", ssh, top .. "/", tgt .. ":" .. src .. "/" })
  local sync = now() - t0
  if rrc ~= 0 then
    local last = util.splitlines(util.strip(rerr))
    util.die(("sync to %s failed (rsync exit %d: %s); the job never ran."):format(a.on, rrc, last[#last] or "?"), 255)
  end
  local exports = {}
  for k, v in pairs(env) do exports[#exports + 1] = k .. "=" .. util.shquote(v) end
  table.sort(exports)
  local set = {}
  for k in pairs(cfg.set or {}) do set[#set + 1] = k end
  table.sort(set)
  for _, k in ipairs(set) do exports[#exports + 1] = ('%s="%s"'):format(k, cfg.set[k]:gsub("{dir}", function() return "$HOME/" .. d end)) end
  local meta = ('"$HOME/%s/jobs/%s"'):format(d, jid)
  -- the copy's own git index marks what the job wrote; nix flakes also see only tracked files
  local script = table.concat({
    ('mkdir -p %s && cd "$HOME/%s" || exit 255'):format(meta, src), "[ -d .git ] || git init -q",
    ("git add -A && git write-tree > %s/tree"):format(meta),
    ("{ (cd %s && %s%s); echo $? > %s/rc; } 2>&1 | tee %s/log"):format(util.shquote(rel),
      #exports > 0 and "export " .. table.concat(exports, " ") .. " && " or "", full, meta, meta),
    ("git ls-files -z -m -o --exclude-standard > %s/files"):format(meta),
    ('exit "$(cat %s/rc 2>/dev/null || echo 255)"'):format(meta) }, "; ")
  local name = ((who .. "-j" .. jid):lower():gsub("[^a-z0-9_-]", "-")):sub(1, 32)
  local hcrun = { "hc", "run", "--on", a.on, "--bg", "--json", "--no-notify", "--name", name, "--label", "swarm-agent=" .. who,
    "--label", "swarm-job=" .. jid, "--label", ("swarm-wt=%s/%s"):format(repo, wtname) }
  if rec.task then
    hcrun[#hcrun + 1] = "--label"
    hcrun[#hcrun + 1] = "swarm-task=" .. util.d(rec.task)
  end
  for _, x in ipairs({ "sh", "-c", script }) do hcrun[#hcrun + 1] = x end
  local ok, o = pcall(json.decode, proc.run(hcrun) or "")
  if not (ok and type(o) == "table" and o.address) then
    util.die(("`hc run --on %s` failed; the job never ran."):format(a.on), 255)
  end
  rec.hc = o.address
  db.log(c, who, "job-start", jid, json.encode(rec))
  local w
  while true do
    local ok2, x = pcall(json.decode, proc.run({ "hc", "wait", rec.hc, "--json", "--timeout", "600" }) or "")
    if not (ok2 and type(x) == "table") then return finish("lost", nil, sync) end
    if x.ended then w = x; break end
  end
  local code = w.exit_code
  if code == nil then code = type(w.signal) == "number" and 128 + w.signal or "lost" end
  local tb = now()
  local function rs(...) proc.exec({ "rsync", "-a", "-e", ssh, ... }) end
  rs(("%s:%s/jobs/%s/"):format(tgt, d, jid), jobs .. "/")
  local back = {}
  for _, f in ipairs(util.split(util.slurp(jobs .. "/files") or "", "\0")) do
    if f ~= "" then back[#back + 1] = f end
  end
  local kept = {}
  if #back > 0 then
    local stage = jobs .. "/kept"
    rs("--from0", "--files-from=" .. jobs .. "/files", ("%s:%s/"):format(tgt, src), stage .. "/")
    local now_h = hashes(top, back)
    for _, f in ipairs(back) do
      if exists(stage .. "/" .. f) then
        if now_h[f] == before[f] and (lfs.symlinkattributes(util.join(top, f)) ~= nil) == (before[f] ~= nil) then  -- untouched here since the sync
          mkdirp(util.dirname(util.join(top, f)))
          proc.exec({ "mv", "-f", stage .. "/" .. f, util.join(top, f) })
        else
          kept[#kept + 1] = f
        end
      end
    end
  end
  local home = os.getenv("HOME") or ""
  for _, b in ipairs(cfg.bring_back or {}) do  -- ~/x: the same path on both machines; else relative to the tree
    if util.startswith(b, "~/") then rs(tgt .. ":" .. b:sub(3), home .. b:sub(2))
    else rs(("%s:%s/%s"):format(tgt, src, b), util.join(top, b)) end
  end
  local tree = util.slurp(jobs .. "/tree")
  proc.run({ "hc", "rm", rec.hc })
  return finish(code, tree and util.strip(tree), sync, now() - tb, kept)
end

return M
