-- swarm state --json (one read-only snapshot for UIs) and swarm watch.
local json, util, db = require "swarm.json", require "swarm.util", require "swarm.db"
local agents, tasks, machine = require "swarm.agents", require "swarm.tasks", require "swarm.machine"
local conflict, proc = require "swarm.conflict", require "swarm.proc"
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
  local ags = {}
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
    local ag = {
      name = x.name, hc = N(x.hc), model = N(x.model), role = N(x.role), stay = N(x.stay), ctx_tokens = x.ctx_tokens or 0, status = N(status),
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
  local avail, total, psi = machine.mem_psi()
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
  local out = {
    active = false, db = p, now = t, view = N(a.view), comms = N(cv),
    tasks = array(tk), agents = array(ags),
    conflicts = fill_all(rows("select * from conflict order by since desc")),
    pressure = array(press), machine = mach,
  }
  for _, x in ipairs(ags) do
    if x.ended == null then out.active = true end
  end
  local deep = a.view == "activity"  -- the Activity tab folds and filters, so it reads further back
  if want.messages then
    local r, n = rows("select id,ts,frm,dest,substr(body,1,500) as body,urgent,kind from msg order by id desc limit "
      .. (deep and 120 or 40))
    out.messages = fill_all(r, n)
  end
  if want.events then
    local r, n = rows("select id,ts,agent,kind,path,data from event where kind not in ('touch','status','heavy-count') "
      .. "order by id desc limit " .. (deep and 300 or 60))
    out.events = pushinfo(fill_all(r, n))
  end
  if want.locks then out.locks = fill_all(rows("select * from lock order by since desc")) end
  if want.running then  -- one /proc scan, only where the System view shows it
    local hv = {}
    local ok, r = pcall(machine.heavy_procs, c, machine.read_procs())
    if ok then hv = r
    elseif not tostring(r):find("no such column", 1, true) then error(r, 0) end  -- an old db without claude_pid
    table.sort(hv, function(x, y)
      if x.rss_kb ~= y.rss_kb then return x.rss_kb > y.rss_kb end
      return x.pid < y.pid
    end)
    local run = {}
    for _, h in ipairs(hv) do
      run[#run + 1] = { agent = h.agent, command = util.cut(h.cmd, 120), elapsed_s = math.floor(h.age),
        start = t - math.floor(h.age), rss_kb = h.rss_kb }
    end
    -- jobs on other machines (local ones are in the /proc scan), with watchd's reading of each job's process tree;
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
