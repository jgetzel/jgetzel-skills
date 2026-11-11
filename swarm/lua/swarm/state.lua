-- swarm state --json (one read-only snapshot for UIs) and swarm watch.
local json, util, db = require "swarm.json", require "swarm.util", require "swarm.db"
local agents, tasks, machine = require "swarm.agents", require "swarm.tasks", require "swarm.machine"
local conflict, proc, cost = require "swarm.conflict", require "swarm.proc", require "swarm.cost"
local unistd = require "posix.unistd"
local signal, lfs = require "posix.signal", require "lfs"
local M = {}

local null, array = json.null, json.array

-- Sections each panel view needs beyond the header (tasks, agents, conflicts, pressure, machine).
-- "lanes": hc idle lookups, worktrees and each live agent's last events. No --view is everything.
M.VIEWS = {
  overview = { lanes = true, messages = true, events = true }, agents = { lanes = true }, board = {},
  activity = { messages = true, events = true }, system = { lanes = true, events = true, locks = true, running = true } }
local ALL = { lanes = true, messages = true, events = true, locks = true, running = true }

local TIMING = { "created_at", "first_claimed_at", "done_at", "dropped_at", "queue_wait_s", "work_s", "total_s", "blocked_s",
  "claims", "releases", "holders", "claim_ctx", "done_ctx", "pr", "merged_at", "ci_conclusion", "merge_to_green_s" }

-- A NULL (nil) column is null in the output, as Python prints it; list is the keys the row always has.
local function fill(row, list)
  for _, k in ipairs(list) do
    if row[k] == nil then row[k] = null end
  end
  return row
end

local function fill_all(rows, names)
  for _, r in ipairs(rows) do fill(r, names) end
  return array(rows)
end

local function N(v)
  if v == nil then return null end
  return v
end

-- `git rev-parse --abbrev-ref HEAD` in worktree wt without a subprocess: read its HEAD file.
local function head_branch(wt)
  local g = util.join(wt, ".git")
  if lfs.attributes(g, "mode") == "file" then  -- a linked worktree: .git names its gitdir
    local dir = (util.slurp(g) or ""):match("gitdir:%s*(.-)%s*$")
    if not dir then return nil end
    g = util.join(wt, dir)
  end
  local s = util.slurp(util.join(g, "HEAD"))
  if not s then return nil end
  s = util.strip(s)
  return util.startswith(s, "ref: refs/heads/") and s:sub(17) or "HEAD"
end

-- fate's checks in the order the agent screen shows them (REDESIGN.md §2), and each one's line
local CHECKS = { "stay", "task", "lock", "unlanded", "job", "unread", "terminal", "waiter", "idle", "context" }
local LABEL = { stay = "Stays", task = "Holds a task", lock = "Holds a lock", unlanded = "Work not on its base",
  job = "Background process", unread = "Unread messages", terminal = "Terminal", waiter = "Waiter", idle = "Idle",
  context = "Context" }

local function dur(s) return util.ago(util.now() - s) end

-- watchd's verdict on live idle agent row x, and the checks behind it: watchd.fate with recording reads. all: every
-- check (the agent screen); else only those fate made, which end at the first that holds (Home's chip).
-- R: watchd.reads; by: hc terminals by address (nil: hc did not answer).
function M.fate(c, x, t, R, by, all)
  local watchd = require "swarm.watchd"
  local hx = by and x.hc and x.hc ~= "" and by[x.hc] or nil
  local g, order, last = R.f(x.name), {}, nil
  g.rec = function(label, v) order[#order + 1] = label; if v then last = label end end
  local v = watchd.fate(x, t, hx, by ~= nil, g)  -- the plain run: watchd's verdict, ending at the check that holds
  local f, on = g, {}
  for _, k in ipairs(order) do on[k] = k == last end
  if all then  -- every check, from a second run in which none holds
    f, on = R.f(x.name), {}
    f.all, f.rec = true, function(label, h) on[label] = h end
    watchd.fate(x, t, hx, by ~= nil, f)
    on.unread = false
  end
  local reuse = v == "reuse"
  if on.context ~= nil then on.context, on.waiter = reuse, reuse end  -- they keep it only together
  if v ~= nil and v ~= "unclean" then last = nil end  -- a verdict past every keeping check: none of them holds
  local pool = tasks.pool(c)
  local w, u = R.waking(x.name)
  if on.unread ~= nil then on.unread = reuse and w > 0 end
  local detail, short = {}, {}
  if on.stay ~= nil then
    local e = c:one("select ts from event where agent=? and kind='stay' order by id desc limit 1", x.name)
    detail.stay = x.stay and ("'%s'%s"):format(x.stay, e and ", for " .. dur(t - e.ts) or "") or "no stay"
    short.stay = "stays"
  end
  if on.task ~= nil then
    local r = c:one("select id,title,lease_until from task where owner=? and state in ('claimed','blocked') order by id", x.name)
    detail.task = r and ("#%d %s%s"):format(r.id, r.title, r.lease_until and (", lease %s left"):format(
      dur(math.max(0, r.lease_until - t))) or "") or "none"
    short.task = r and ("holds #%d"):format(r.id) or "holds a task"
  end
  if on.lock ~= nil then
    local l = {}
    for _, r in ipairs(c:all("select path from lock where agent=? order by path", x.name)) do l[#l + 1] = r.path end
    detail.lock, short.lock = #l > 0 and table.concat(l, ", ") or "none", "holds a lock"
  end
  if on.unlanded ~= nil then
    if f.held then
      local files, commits = 0, 0
      for _, l in ipairs(util.splitlines(watchd.unclean_list(f.held, f.B[1]))) do
        if l:match("^commit ") then commits = commits + 1 elseif l ~= "" then files = files + 1 end
      end
      local pr = c:one("select pr from task where owner=? and pr is not null order by id desc limit 1", x.name)
      detail.unlanded = ("%s: %d uncommitted file%s, %d commit%s not on %s%s"):format(f.held, files, files == 1 and "" or "s",
        commits, commits == 1 and "" or "s", f.B[1], pr and (" (PR #%d)"):format(pr.pr) or "")
      short.unlanded = files > 0 and "uncommitted work" or "unlanded commits"
    else
      detail.unlanded = "all on its base"
    end
  end
  if on.job ~= nil then
    detail.job = f.proc and ("%s, %s"):format(util.cut(f.proc.args, 80), dur(f.proc.age or 0)) or "none"
    short.job = "background job"
  end
  detail.unread = w > 0 and ("%d%s"):format(w, u > 0 and (", %d urgent"):format(u) or "") or "none"
  if on.terminal ~= nil then
    local other = hx and hx.cwd and hx.cwd ~= "" and not f.ours(hx.cwd)
    detail.terminal = not (x.hc and x.hc ~= "") and "none bound" or not by and x.hc .. ": hc did not answer"
      or not hx and x.hc .. " gone" or other and ("%s in another repo (%s)"):format(x.hc, hx.cwd)
      or ("%s %s"):format(x.hc, hx.status or "?")
    short.terminal = not hx and "terminal gone" or other and "in another repo" or "terminal " .. (hx.status or "busy")
  end
  if on.waiter ~= nil then
    detail.waiter = x.waiter and f.alive(x.waiter) and ("present (pid %d)"):format(x.waiter) or "gone: no message can wake it"
  end
  if on.idle ~= nil then
    detail.idle = x.status ~= "idle" and tostring(x.status) or ("%s (watchd waits 2m)"):format(dur(t - (x.last_active or 0)))
    short.idle = x.status ~= "idle" and tostring(x.status) or "idle under 2 min"
  end
  if on.context ~= nil then
    local k = math.floor((x.ctx_tokens or 0) / 1000)
    detail.context = (x.ctx_tokens or 0) >= agents.SMALL_CTX and ("%dk: too big to be given another task"):format(k)
      or #pool == 0 and ("%dk: small enough, but no task is ready"):format(k)
      or f.passed_over() and ("%dk: small enough, but it passed over the ready tasks"):format(k)
      or ("%dk: small enough for another task; #%d is ready"):format(k, pool[1].id)
    short.context = pool[1] and ("#%d is ready"):format(pool[1].id) or "a task is ready"
  end
  local checks, held = {}, {}
  for _, k in ipairs(CHECKS) do
    if on[k] ~= nil then
      checks[#checks + 1] = { label = LABEL[k], on = on[k], detail = detail[k] or "" }
      if on[k] and k ~= "waiter" and k ~= "unread" then held[#held + 1] = short[k] end
    end
  end
  local verdict = v or "kept"
  return { verdict = verdict,
    says = verdict == "end" and "watchd ends it at its next tick" or verdict == "reuse" and "Kept for reuse: " .. short.context
      or "Kept: " .. table.concat(held, " and "),
    short = verdict == "end" and "ending" or verdict == "reuse" and short.context or N(last and short[last]),
    checks = array(all and checks or {}) }
end

local function pid_alive(pid)
  pid = tonumber(pid)
  return pid ~= nil and signal.kill(pid, 0) == 0
end

function M.cmd_state(a)
  local p, t = db.dbpath(), util.now()
  if not lfs.attributes(p, "mode") then
    print(json.encode({ active = false, db = p, now = t }))
    return
  end
  local c = db.open_ro(p)
  if not c then util.die("can't open " .. p) end

  -- a table an older db never had reads as no rows
  local function rows(q, ...)
    local ok, r, names = pcall(c.all_cols, c, q, ...)
    if ok then return r, names end
    if not tostring(r):find("no such table", 1, true) then error(r, 0) end
    return {}, {}
  end

  local tk, tnames = rows("select * from task order by id")
  local tev = rows("select ts,agent,kind,data from event where kind in ('" .. table.concat(tasks.TASK_KINDS, "','")
    .. "') order by id")
  local by_task = {}
  for _, e in ipairs(tev) do
    local id = tasks.event_task(e)
    if id then by_task[id] = by_task[id] or {}; table.insert(by_task[id], e) end
  end
  local state = {}
  for _, r in ipairs(tk) do state[r.id] = r.state end
  local tkeys = { "lease_left", "deps", "waiting", "blocks" }
  for _, k in ipairs(tnames) do if k ~= "body" then tkeys[#tkeys + 1] = k end end
  for _, k in ipairs(TIMING) do tkeys[#tkeys + 1] = k end
  for _, r in ipairs(tk) do
    r.body = nil
    for k, v in pairs(tasks.task_timing(r, by_task[r.id] or {})) do r[k] = v end
    r.holders = array(r.holders)
    r.lease_left = (r.state == "claimed" or r.state == "blocked") and r.lease_until and r.lease_until ~= 0
      and r.lease_until - t or nil
    r.deps = tasks.deps_of(r)
    r.waiting = false
    for _, d in ipairs(r.deps) do
      if state[d] ~= "done" then r.waiting = true end
    end
  end
  for _, r in ipairs(tk) do
    local blocks = {}
    for _, x in ipairs(tk) do
      if x.state == "open" and r.state ~= "done" then
        for _, d in ipairs(x.deps) do
          if d == r.id then blocks[#blocks + 1] = x.id; break end
        end
      end
    end
    r.blocks = blocks
  end
  for _, r in ipairs(tk) do
    r.deps, r.blocks = array(r.deps), array(r.blocks)
    fill(r, tkeys)
  end

  local full = a.view == nil
  local want = a.view and M.VIEWS[a.view] or ALL
  local lanes = want.lanes
  local wts = lanes and conflict.wt_map(c) or {}
  local ags, R, by = {}, nil, nil
  for _, x in ipairs(rows("select * from agent order by ended is not null, name")) do
    local own = {}
    for _, r in ipairs(tk) do
      if r.owner == x.name and (r.state == "claimed" or r.state == "blocked") then own[#own + 1] = r end
    end
    local sn = x.snap and util.startswith(x.snap, "{") and json.decode(x.snap) or {}
    local live = x.ended == nil
    local wt = wts[x.name] or x.wt
    if wt == "" then wt = nil end
    local act = (live and lanes) and agents.session_active(x, t) or (x.last_active or 0)  -- hc lookups only where idle shows
    local status = x.status
    if not live then status = "ended"
    else
      for _, r in ipairs(own) do if r.state == "blocked" then status = "blocked" end end
    end
    -- a stayer's hung sign (watchd.hung): its worst stay-* event since it was last active
    local sign
    if live and x.stay and x.stay ~= "" and x.status == "idle" then
      local got = {}
      for _, e in ipairs(rows("select distinct kind from event where agent=? and kind in ('stay-hung','stay-nowaiter','stay-unwoken') "
        .. "and ts>=?", x.name, x.last_active or 0)) do got[e.kind] = true end
      sign = got["stay-hung"] and "hung" or got["stay-nowaiter"] and "nowaiter" or got["stay-unwoken"] and "unwoken" or nil
    end
    local ag = {
      name = x.name, hc = N(x.hc), model = N(x.model), role = N(x.role), stay = N(x.stay), stay_sign = N(sign), ctx_tokens = x.ctx_tokens or 0, status = N(status),
      idle_s = t - (act == 0 and t or act), started = N(x.started), ended = N(x.ended),
      cache = t - act < agents.COLD_IDLE and "warm" or "cold",
      cold_guarded = (live and lanes and agents.cold_reason(x, t)) and true or false,
      worktree = N(wt), branch = (live and wt) and N(head_branch(wt)) or null,
      cold_at = (live and x.status ~= "working") and act + agents.COLD_IDLE or null,
      task = own[1] and { id = own[1].id, title = own[1].title, state = own[1].state } or null,
      files = array((full or live or x.name == a.agent) and type(sn) == "table" and sn.files or nil),
    }
    if full then
      local lk = {}
      for _, r in ipairs(rows("select path from lock where agent=?", x.name)) do lk[#lk + 1] = r.path end
      ag.locks = array(lk)
    end
    if full or (lanes and live) or x.name == a.agent then
      ag.events = fill_all(rows("select ts,kind,path,data from event where agent=? and kind not in ('touch','status') "
        .. "order by id desc limit 5", x.name))
    end
    if live and x.status == "idle" and (lanes or x.name == a.agent) then  -- watchd's verdict and why (REDESIGN.md §2)
      local ok, r = pcall(function()
        if not R then
          local watchd = require "swarm.watchd"
          local terms = agents.hc_terminals()
          if terms then
            by = {}
            for _, h in ipairs(terms) do if h.address then by[h.address] = h end end
          end
          R = watchd.reads(c, watchd.main_wt(), lanes and wts or conflict.wt_map(c), conflict.worktrees(), tasks.pool(c))
        end
        return M.fate(c, x, t, R, by, x.name == a.agent)
      end)
      if not ok and not tostring(r):find("no such", 1, true) then error(r, 0) end  -- an old db: no verdict
      ag.fate = ok and r or null
    end
    if full or x.name == a.agent then  -- the detail pane's messages
      ag.messages = array(rows("select id,ts,frm,dest,substr(body,1,500) as body,urgent,kind from msg "
        .. "where frm=? or dest=? order by id desc limit 5", x.name, x.name))
    end
    ags[#ags + 1] = ag
  end

  local episodes = {}
  for _, e in ipairs(rows("select ts,kind,data from event where kind in ('pressure','pressure-end') order by id")) do
    if e.kind == "pressure" then
      episodes[#episodes + 1] = { start = e.ts, ["end"] = null, line = N(e.data) }
    elseif #episodes > 0 and episodes[#episodes]["end"] == null then
      episodes[#episodes]["end"] = e.ts
    end
  end
  local press = {}
  for i = #episodes, math.max(1, #episodes - 4), -1 do press[#press + 1] = episodes[i] end

  local mach = null
  local avail, total, psi = machine.mem()
  if avail then
    mach = { line = machine.machine_line(avail, total, psi), avail_kb = avail, total_kb = total, psi = psi,
      high = machine.pressure_high(avail, total, psi) }
  end

  -- push events keep {branch, subject} JSON in path; older ones have none
  local function pushinfo(evs)
    for _, e in ipairs(evs) do
      if e.kind == "push" then
        local d = e.path and json.decode(e.path)
        if type(d) ~= "table" then d = {} end
        e.branch, e.subject, e.path = N(d.branch), N(d.subject), null
      end
    end
    return evs
  end
  for _, x in ipairs(ags) do
    if x.events then pushinfo(x.events) end
  end

  local cm = rows("select v from meta where k='comms'")[1]
  local cv = cm and cm.v ~= "" and cm.v or agents.env("SWARM_COMMS")
  local function meta(k) local r = rows("select v from meta where k=?", k)[1]; return r and r.v end
  local nlive = 0
  for _, x in ipairs(ags) do
    if x.ended == null and x.name ~= cv then nlive = nlive + 1 end
  end
  local out = {
    active = false, db = p, now = t, view = N(a.view), comms = N(cv),
    -- the user's staffing numbers (agents.limits) and the board's "auto-spawn holding" line while it holds
    limits = { live = nlive, min = N(tonumber(meta("agent_min"))), max = N(tonumber(meta("agent_max"))), held = N(meta("spawn_held")) },
    tasks = array(tk), agents = array(ags),
    conflicts = fill_all(rows("select * from conflict order by since desc")),
    pressure = array(press), machine = mach,
  }
  for _, x in ipairs(ags) do
    if x.ended == null then out.active = true end
  end
  -- the latest runs on the base, from the ci table watchd fills, and how many of the newest finished ones are red
  local runs = rows("select id,status,conclusion,url,created from ci order by created desc limit 5")
  local streak = 0
  for _, r in ipairs(rows("select conclusion from ci where status='completed' and conclusion!='cancelled' order by created desc limit 50")) do
    if r.conclusion == "success" then break end
    streak = streak + 1
  end
  out.ci = { runs = fill_all(runs, { "id", "status", "conclusion", "url", "created" }), red_streak = streak }
  -- watchd: its record (pid, terminal), what it was started with, and whether the swarm code changed since it started
  local wr = meta("watchd")
  local run_ = meta("watchd_run")
  run_ = run_ and json.decode(run_)
  run_ = type(run_) == "table" and run_ or {}
  if wr then
    local pid, term = wr:match("^(%S+)%s*(%S*)")
    local newest = 0
    for f in lfs.dir(util.join(os.getenv("SWARM_HERE") or ".", "lua", "swarm")) do
      local m = f:match("%.lua$") and lfs.attributes(util.join(os.getenv("SWARM_HERE"), "lua", "swarm", f), "modification")
      if m and m > newest then newest = m end
    end
    out.watchd = { pid = tonumber(pid), terminal = term ~= "" and term ~= "-" and term or null, started = N(run_.started),
      alive = pid_alive(pid), stale = run_.started ~= nil and newest > run_.started,
      flags = run_.flags and array(run_.flags) or null }
  else
    out.watchd = null
  end
  local aw = meta("away")  -- "<since> <note>" while the user is away (`swarm away`)
  out.away = aw and { since = tonumber(aw:match("^%d+")), note = N(aw:match("^%d+ (.+)$")) } or null
  out.back = json.decode(meta("away_digest") or "") or null  -- `swarm away --back`'s digest, until the next away
  if a.task then  -- the task screen: what the board's rows leave out
    local r = rows("select body from task where id=?", a.task)[1]
    local evs, ms = {}, {}
    for _, e in ipairs(tev) do
      if tasks.event_task(e) == a.task then evs[#evs + 1] = e end
    end
    for _, m in ipairs(rows("select id,ts,frm,dest,substr(body,1,500) as body,urgent,kind from msg where body like ? order by id desc limit 200",
        "%#" .. a.task .. "%")) do
      if #ms < 20 and (m.body .. " "):find("#" .. a.task .. "%D") then ms[#ms + 1] = m end
    end
    out.task = r and { id = a.task, body = N(r.body), events = array(evs), messages = array(ms) } or null
  end
  local deep = a.view == "activity"  -- the Activity tab folds and filters, so it reads further back
  if want.messages then
    local r, n = rows("select id,ts,frm,dest,substr(body,1,500) as body,urgent,kind from msg order by id desc limit "
      .. (deep and 120 or 40))
    out.messages = fill_all(r, n)
  end
  if want.events then
    local r, n = rows("select id,ts,agent,kind,path,data from event where kind not in ('touch','status') "
      .. "order by id desc limit " .. (deep and 300 or 60))
    out.events = pushinfo(fill_all(r, n))
  end
  if want.locks then out.locks = fill_all(rows("select * from lock order by since desc")) end
  if want.running then  -- one ps, only where the System view shows it
    local hv = {}
    local ok, r = pcall(machine.holders, c, machine.procs())
    if ok then hv = r
    elseif not tostring(r):find("no such column", 1, true) then error(r, 0) end  -- an old db without claude_pid
    local run = {}
    for _, h in ipairs(hv) do
      run[#run + 1] = { agent = h.agent, command = util.cut(h.top or "", 120), elapsed_s = math.floor(h.age or 0),
        start = t - math.floor(h.age or 0), rss_kb = h.kb, top_kb = h.top and h.top_kb or null }
    end
    -- from the cmd-cost history, this repo on this machine: the last finished commands that cost something, and
    -- the most intensive by peak (`swarm cost --top`)
    local rc, top = {}, {}
    if unistd.access(cost.path(), "r") then
      local h, host, repo = cost.open(), cost.hostname(), cost.repo_name() or "?"
      rc = h:all("select ts,agent,cmd,wall_s,peak_kb from cmd where machine=? and repo=? order by id desc limit 6", host, repo)
      top = h:all("select key,count(*) n,max(peak_kb) peak_kb,max(wall_s) wall_s,max(cpu_s) cpu_s from cmd where machine=? and repo=? "
        .. "group by key order by max(peak_kb) desc limit 5", host, repo)
    end
    out.costly, out.cost_top = array(rc), array(top)
    -- jobs on other machines (local ones are in the ps scan), with watchd's reading of each job's process tree;
    -- lost: its `swarm run` is gone and so is its terminal; unreachable: watchd's probe of the machine failed
    local js, gone = {}, {}
    if #rows("select 1 from event where kind='job-start' limit 1") > 0 then
      for _, j in ipairs(machine.live_jobs(c, t)) do
        if j.machine then
          js[#js + 1] = j
          if not pid_alive(j.pid) then gone[#gone + 1] = j end
        end
      end
    end
    local live = {}
    if #gone > 0 then
      for _, x in ipairs(agents.hc_terminals() or {}) do live[x.address] = true end
    end
    local isgone = {}
    for _, j in ipairs(gone) do isgone[j] = true end
    local mr = #js > 0 and c:one("select v from meta where k='machines'")
    local ms = mr and json.decode(mr.v) or {}
    for _, j in ipairs(js) do
      local m = type(ms[j.machine]) == "table" and ms[j.machine] or {}
      local r = type(m.jobs) == "table" and type(m.jobs[j.id]) == "table" and m.jobs[j.id] or {}
      local unreach = m.state ~= nil and m.state ~= "connected"
      local gone = r.gone ~= nil or (r.rss_kb == nil and not live[j.hc])  -- the probe's word, else `hc ls` here
      run[#run + 1] = { agent = j.agent, command = util.cut(j.cmd or "", 120), elapsed_s = t - j.ts, start = j.ts,
        rss_kb = r.rss_kb or null, cpu = r.cpu or null, machine = j.machine, job = j.id, unreachable = unreach,
        lost = (not unreach and isgone[j] and gone) and true or false }
    end
    out.running = array(run)
  end
  print(json.encode(out))
end

function M.cmd_watch(c, a)
  local posix_time = require "posix.time"
  local last = math.max(0, ((c:one("select max(id) as m from event") or {}).m or 0) - a.tail)
  local tick = 0
  while true do
    for _, e in ipairs(c:all("select * from event where id>? order by id", last)) do
      last = e.id
      local sum = 0
      for i = 1, #(e.agent or "") do sum = sum + e.agent:byte(i) end
      local col = ({ "31", "32", "33", "34", "35", "36" })[sum % 6 + 1]
      io.write(("%s \27[%sm%-12s\27[0m %-9s %s %s\n"):format(os.date("%H:%M:%S", e.ts), col, e.agent or "-", e.kind,
        e.path or "", e.data or ""))
      io.stdout:flush()
    end
    if tick % 30 == 0 then
      local parts = {}
      for _, x in ipairs(agents.live_agents(c)) do parts[#parts + 1] = x.name .. ":" .. x.status end
      io.write("\27[2m-- " .. table.concat(parts, " | ") .. " --\27[0m\n")
      io.stdout:flush()
    end
    tick = tick + 1
    if a.once then return end
    posix_time.nanosleep({ tv_sec = 1, tv_nsec = 0 })
  end
end

return M
