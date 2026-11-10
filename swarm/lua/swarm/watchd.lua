-- Reaping and watchd: reap, landed, end_agent, sweep_worktrees, lifecycle, machine_tick; cmd watchd/spawn.
local util, proc, json, re, db = require "swarm.util", require "swarm.proc", require "swarm.json", require "swarm.re", require "swarm.db"
local agents, msgs, tasks, conflict, machine = require "swarm.agents", require "swarm.msgs", require "swarm.tasks",
  require "swarm.conflict", require "swarm.machine"
local run, ci = require "swarm.run", require "swarm.ci"
local lfs = require "lfs"
local unistd, stdlib, signal = require "posix.unistd", require "posix.stdlib", require "posix.signal"
local pstat = require "posix.sys.stat"
local M = {}

M.LEASE = tasks.LEASE
M.HC_Q = "a prompt needs the human"
M.SWEEP_IDLE = 1800  -- a worktree untouched this long (s) may be swept
M.NOT_LANDED = {}    -- worktree\0HEAD\0B verdicts "not landed", so unchanged worktrees don't hit gh every tick

local d = util.d

local function nz(s)  -- Python truthiness for a string: nil and "" are false
  if s == nil or s == "" then return nil end
  return s
end

local function exists(p)
  return p ~= nil and lfs.attributes(p) ~= nil
end

local function isdir(p)
  return p ~= nil and lfs.attributes(p, "mode") == "directory"
end

local function realpath(p)  -- os.path.realpath: a missing path comes back as given
  return stdlib.realpath(p) or p
end

local function makedirs(p)
  if p == "" or exists(p) then return end
  makedirs(util.dirname(p))
  lfs.mkdir(p)
end

local function replace(s, old, new)  -- str.replace, no patterns
  local r, i = {}, 1
  while true do
    local j = s:find(old, i, true)
    if not j then break end
    r[#r + 1] = s:sub(i, j - 1) .. new
    i = j + #old
  end
  r[#r + 1] = s:sub(i)
  return table.concat(r)
end

function M.inside(p, wt)
  return p == wt or util.startswith(p, wt .. "/")
end

-- ---------- reap ----------

-- Reopen expired task leases, drop expired locks, end dead agents.
-- live_addrs: set of live hc terminal addresses, or nil to skip the dead-agent check.
function M.reap(c, live_addrs, t, comms)
  t = t or util.now()
  local out, bg = {}, nil
  for _, r in ipairs(c:all("select * from task where state='claimed' and lease_until<?", t)) do
    local o = c:one("select * from agent where name=?", r.owner)
    if o and o.ended == nil and o.status == "idle" and not bg then bg = machine.bg_agents(c, machine.read_procs()) end
    if o and o.ended == nil and (o.status ~= "idle" or bg[o.name])
        and not (live_addrs and nz(o.hc) and not live_addrs[o.hc]) then
      -- a working, prompt-blocked or background-waiting owner past its lease: its work is live: tell the communicator, keep it
      if comms and not c:one("select 1 from event where kind='lease-late' and path=? and ts>?", d(r.id), t - M.LEASE) then
        db.log(c, r.owner, "lease-late", d(r.id))
        msgs.post(c, "swarm", comms, ("%s has held #%s past its lease (idle %s)."):format(r.owner, d(r.id), util.ago(o.last_active)),
          false, "notice")
      end
    else
      c:tx(function()  -- re-check: a renew or re-claim since the select keeps the task
        if c:exec("update task set state='open', owner=null, lease_until=null "
            .. "where id=? and owner=? and state='claimed' and lease_until<?", r.id, r.owner, t) == 0 then
          return
        end
        msgs.post(c, "swarm", r.owner, ("released #%s (%s): lease expired while idle; renew on long work. "
          .. "`swarm task claim %s` to take it back."):format(d(r.id), r.title, d(r.id)), false, "system")
        db.log(c, r.owner, "reap", nil, ("task #%s lease expired"):format(d(r.id)))
        out[#out + 1] = "task #" .. d(r.id)
      end)
    end
  end
  for _, r in ipairs(c:all("select * from lock where lease_until<?", t)) do
    c:tx(function()  -- re-check: a fresh lock on the path since the select stays
      if c:exec("delete from lock where path=? and agent=? and lease_until<?", r.path, r.agent, t) == 0 then return end
      db.log(c, r.agent, "reap", r.path, "lock expired")
      out[#out + 1] = "lock " .. r.path
    end)
  end
  if live_addrs then
    for _, a in ipairs(agents.live_agents(c)) do
      if nz(a.hc) and not live_addrs[a.hc] then
        c:tx(function()  -- re-check: still bound to the address judged dead, still live
          if c:exec("update agent set ended=?, status='ended' where name=? and hc=? and ended is null", t, a.name, a.hc) == 0 then
            return
          end
          agents._release(c, a.name)
          msgs.post(c, "swarm", "@all", a.name .. " is gone; its tasks and locks are released.", false, "system")
          db.log(c, a.name, "reap", nil, "agent gone")
          out[#out + 1] = "agent " .. a.name
        end)
      end
    end
  end
  return out
end

-- ---------- landed, end_agent ----------

-- Commits of ref (checked from cwd) are in B: ancestor, same content under other commits, or a PR merged at this
-- commit. The branch name alone proves nothing: a branch reused after its PR merged holds unmerged commits.
function M.landed_ref(cwd, ref, B)
  if proc.gx({ "-C", cwd, "merge-base", "--is-ancestor", ref, B }) == 0 then return true end
  local mb = nz(proc.git({ "-C", cwd, "merge-base", B, ref }))
  local files = {}
  if mb then
    for f in (proc.run({ "git", "-C", cwd, "diff", "--name-only", "-z", mb, ref }) or ""):gmatch("[^%z]+") do files[#files + 1] = f end
  end
  if #files > 0 then
    local args = { "-C", cwd, "diff", "--quiet", ref, B, "--" }
    for _, f in ipairs(files) do args[#args + 1] = f end
    if proc.gx(args) == 0 then return true end  -- squash or rebase merge: same content under other commits
  end
  local br = nz(proc.git({ "-C", cwd, "rev-parse", "--abbrev-ref", ref }))
  local head = nz(proc.git({ "-C", cwd, "rev-parse", ref }))
  local prs = br and head and proc.run({ "gh", "pr", "list", "--head", br, "--state", "merged", "--json", "number,headRefOid" }, cwd)
  local j = prs and json.decode(prs)
  for _, pr in ipairs(type(j) == "table" and j or {}) do
    if pr.headRefOid == head then return true end
  end
  return false
end

-- Nothing in worktree wt is unlanded relative to ref B (sw-lifecycle §4.2).
function M.landed(wt, B, main)
  if not exists(wt) then  -- nothing uncommitted can be lost; judge by its branch if git still knows it
    local m = re.search("^worktree " .. re.escape(wt) .. "\\n(?:.*\\n)*?branch refs/heads/(.*)$",
      proc.run({ "git", "-C", main, "worktree", "list", "--porcelain" }) or "", re.M)
    return not m or M.landed_ref(main, m[1], B)
  end
  local st = proc.run({ "git", "-C", wt, "status", "--porcelain" })
  if st == nil or util.strip(st) ~= "" then return false end
  return wt == main or M.landed_ref(wt, "HEAD", B)
end

-- Release a finished agent, kill its terminal, and remove its worktree and branch without losing work.
function M.end_agent(c, a, wt, main, comms)
  local n = a.name
  local br = wt and nz(proc.git({ "-C", wt, "rev-parse", "--abbrev-ref", "HEAD" }))
  local ok = c:tx(function()  -- re-check what lifecycle judged: still idle, same terminal, no claim, no lock
    if not c:one([[select 1 from agent where name=? and ended is null and status='idle' and hc is ?
        and not exists (select 1 from task where owner=? and state in ('claimed','blocked'))
        and not exists (select 1 from lock where agent=?)]], n, a.hc, n, n) then
      return false
    end
    agents._release(c, n)
    c:exec("update agent set ended=?, status='ended' where name=?", util.now(), n)
    db.log(c, n, "end", nil, "landed")
    return true
  end)
  if not ok then return end
  if nz(a.hc) then
    proc.run({ "hc", "kill", a.hc })
    proc.run({ "hc", "rm", a.hc })
  end
  if not nz(wt) or wt == main then return end
  local real = realpath(wt)
  for _, x in ipairs(agents.live_agents(c)) do
    for _, p in ipairs({ x.wt or "", x.cwd or "" }) do
      if p ~= "" and M.inside(realpath(p), real) then return end  -- a live peer uses this worktree
    end
  end
  run.clean_remote(c, real)
  if not exists(wt) then
    proc.run({ "git", "-C", main, "worktree", "prune" })
    return
  end
  local steps = { { "-C", main, "worktree", "remove", wt } }
  if br and br ~= "HEAD" and br ~= "main" and br ~= "master" then
    steps[#steps + 1] = { "-C", main, "branch", "-D", br }
    if nz(proc.git({ "-C", main, "remote", "get-url", "origin" })) and nz(proc.git({ "-C", main, "ls-remote", "--heads", "origin", br })) then
      steps[#steps + 1] = { "-C", main, "push", "-q", "origin", "--delete", br }
    end
  end
  for _, st in ipairs(steps) do
    local rc, err = proc.gx(st)
    if rc ~= 0 then
      if comms then
        msgs.post(c, "swarm", comms, ("%s ended; %s not removed: %s."):format(n, wt, err ~= "" and util.splitlines(err)[1] or "git failed"),
          false, "notice")
      end
      return
    end
  end
end

function M.mem_available_gib()
  local kb = tonumber((util.slurp("/proc/meminfo") or ""):match("MemAvailable:%s+(%d+)"))
  return kb and kb / 2 ^ 20 or math.huge
end

-- ---------- sweep ----------

-- Remove clean, landed worktrees (and their local branch) that no live agent or process uses. Returns {{path, branch, MB}}.
function M.sweep_worktrees(c, comms, dry)
  local lines = util.splitlines(proc.run({ "git", "worktree", "list", "--porcelain" }))
  if #lines == 0 then return {} end
  local main = realpath(lines[1]:sub(10))
  local B = nz(proc.git({ "-C", main, "remote", "get-url", "origin" })) and "origin/main" or "main"
  local wts, cur = {}, nil
  for i = 2, #lines do
    local l = lines[i]
    if util.startswith(l, "worktree ") then
      cur = { realpath(l:sub(10)) }
      wts[#wts + 1] = cur
    elseif util.startswith(l, "branch refs/heads/") and cur then
      cur[2] = l:sub(19)
    end
  end
  local used = {}
  for _, a in ipairs(agents.live_agents(c)) do
    for _, p in ipairs({ a.wt or "", a.cwd or "" }) do
      if p ~= "" then used[#used + 1] = realpath(p) end
    end
  end
  for _, w in pairs(conflict.wt_map(c)) do used[#used + 1] = w end
  local pcwd = {}
  local ok, it, dir = pcall(lfs.dir, machine.PROC)
  if not ok then return {} end  -- no /proc (macOS): which worktrees a process sits in is unknown, so sweep none
  for e in it, dir do
    local l = unistd.readlink(machine.PROC .. "/" .. e .. "/cwd")
    if l then pcwd[#pcwd + 1] = realpath(l) end
  end
  local function in_any(list, wt)
    for _, p in ipairs(list) do
      if M.inside(p, wt) then return true end
    end
    return false
  end
  local t, out, freed = util.now(), {}, 0
  for _, w in ipairs(wts) do
    local wt, br = w[1], w[2]
    if not (wt == main or not isdir(wt) or in_any(used, wt) or in_any(pcwd, wt)) then
      local gd = nz(proc.git({ "-C", wt, "rev-parse", "--absolute-git-dir" }))
      local last = 0
      for _, p in ipairs({ wt, util.join(gd or wt, "logs", "HEAD") }) do
        last = math.max(last, lfs.attributes(p, "modification") or 0)
      end
      local st = proc.run({ "git", "-C", wt, "status", "--porcelain" })
      if not (t - last < M.SWEEP_IDLE or st == nil or util.strip(st) ~= "") then  -- dirty or unreadable: never landed
        local key = table.concat({ wt, proc.git({ "-C", wt, "rev-parse", "HEAD" }) or "", proc.git({ "-C", main, "rev-parse", B }) or "" }, "\0")
        if not M.NOT_LANDED[key] then
          if not M.landed(wt, B, main) then
            M.NOT_LANDED[key] = true
          else
            local mb = math.floor((tonumber((proc.run({ "du", "-sk", wt }) or "0"):match("%d+")) or 0) / 1024)
            local removed = true
            if not dry then
              if proc.gx({ "-C", main, "worktree", "remove", wt }) ~= 0 then
                removed = false
              else
                if br and br ~= "main" and br ~= "master" then proc.gx({ "-C", main, "branch", "-D", br }) end
                db.log(c, nil, "sweep", wt, ("%s %dMB"):format(br or "None", mb))
              end
            end
            if removed then
              out[#out + 1] = { wt, br, mb }
              freed = freed + mb
            end
          end
        end
      end
    end
  end
  if #out > 0 and comms and not dry then
    msgs.post(c, "swarm", comms, ("swept %d landed worktree(s), %d MB freed."):format(#out, freed), false, "notice")
  end
  return out
end

-- ---------- lifecycle ----------

-- End finished agents, digest reusable ones, spawn fresh ones for startable tasks (sw-lifecycle §4).
function M.lifecycle(c, t, comms, terms, opts)
  local wts = conflict.wt_map(c)
  local main = (proc.run({ "git", "worktree", "list", "--porcelain" }) or ""):match("^worktree ([^\n]*)")
  main = main and realpath(main)
  local B = "main"
  if nz(proc.git({ "remote", "get-url", "origin" })) then
    proc.run({ "git", "fetch", "-q", "origin", "main" })
    B = "origin/main"
  end
  M.sweep_worktrees(c, comms)
  local by = {}
  for _, x in ipairs(terms or {}) do
    if x.address then by[x.address] = x end
  end
  local pool = tasks.pool(c)
  local function told_of(n)  -- the task ids n's digests named
    local told = {}
    for _, e in ipairs(c:all("select data from event where kind='digest' and agent=?", n)) do
      for i in (e.data or ""):gmatch("[^,]+") do told[tonumber(i)] = true end
    end
    return told
  end
  -- n was told of every startable task, has read what would wake it, and is idle again: it passed them over
  local function passed_over(n)
    local told = told_of(n)
    for _, r in ipairs(pool) do if not told[r.id] then return false end end
    for _, m in ipairs(msgs.unread(c, n)) do
      if m.kind ~= "notice" or (m.urgent or 0) ~= 0 then return false end
    end
    return true
  end
  local reusable = {}
  for _, a in ipairs(agents.live_agents(c)) do
    local n = a.name
    local x = nz(a.hc) and terms ~= nil and by[a.hc] or nil
    if not (n == comms or a.status ~= "idle" or t - (a.last_active or 0) < 120
        or (nz(a.hc) and terms ~= nil and (not x or (x.status ~= "idle" and x.status ~= "done")))
        or c:one("select 1 from task where owner=? and state in ('claimed','blocked')", n)
        or c:one("select 1 from lock where agent=?", n)
        or (wts[n] and not M.landed(wts[n], B, main))) then
      -- one that passed the work over is ended, not kept as a reason to spawn no one
      if (a.ctx_tokens or 0) < agents.SMALL_CTX and #pool > 0 and not passed_over(n) then
        reusable[#reusable + 1] = a
      else
        M.end_agent(c, a, wts[n], main, comms)
      end
    end
  end
  local ids = {}
  for i, r in ipairs(pool) do ids[i] = r.id end
  table.sort(ids)
  for _, a in ipairs(reusable) do  -- edge-triggered: only when the pool holds an id this agent was never told about
    local told = told_of(a.name)
    local new = false
    for _, i in ipairs(ids) do
      if not told[i] then new = true end
    end
    if new then
      local s = {}
      for k, i in ipairs(ids) do s[k] = d(i) end
      db.log(c, a.name, "digest", nil, table.concat(s, ","))
      msgs.post(c, "swarm", a.name, ("%d open task(s) and you are idle: `swarm board`."):format(#pool), false, "system")
    end
  end
  if #reusable > 0 or #pool == 0 or opts.max_agents == nil then return end
  local members, models, count = {}, {}, {}
  for _, a in ipairs(agents.live_agents(c)) do
    if a.name ~= comms then
      members[#members + 1] = a
      if nz(a.model) then
        if not count[a.model] then models[#models + 1] = a.model end
        count[a.model] = (count[a.model] or 0) + 1
      end
    end
  end
  local common  -- the most common model; a tie goes to the first seen
  for _, m in ipairs(models) do
    if not common or count[m] > count[common] then common = m end
  end
  common = common or "sonnet"
  local prefix = util.endswith(comms, "comms") and comms:sub(1, -6) or comms .. "-"
  local top = 0
  for _, r in ipairs(c:all("select name from agent")) do
    local m = re.fullmatch(re.escape(prefix) .. "(\\d+)", r.name)
    if m then top = math.max(top, tonumber(m[1])) end
  end
  local bo = c:one("select v from meta where k='spawn_backoff'")  -- "until,delay,name" after a failed launch
  local bo_until, bo_delay, bo_name = 0, 0, nil
  if bo then
    local u, dl, nm = bo.v:match("^(%d+),(%d+),(.*)$")
    bo_until, bo_delay, bo_name = tonumber(u), tonumber(dl), nm
  end
  if util.now() < bo_until then return end
  local halt = c:one("select v from meta where k='spawn_halt'")  -- a task auto-spawn gave up on
  if halt then
    local still = false
    for _, t in ipairs(pool) do if tostring(t.id) == halt.v then still = true end end
    if not still then c:exec("delete from meta where k='spawn_halt'"); halt = nil end  -- claimed, done or dropped: lifted
  end
  for _, task in ipairs(pool) do
    if halt and tostring(task.id) == halt.v then goto next_task end
    if #members >= opts.max_agents or M.mem_available_gib() < (opts.min_free_gib or 4) then break end
    local name = nz(bo_name)
    if not name then top = top + 1; name = prefix .. d(top) end
    local model = nz(task.model) or nz(opts.model) or common
    local ok, e = pcall(M.cmd_spawn, c, { name = name, model = model, effort = nz(task.effort) or nz(opts.effort), task_id = task.id, task = {} })
    if ok then
      c:exec("delete from meta where k='spawn_backoff'")
      c:exec("delete from meta where k='spawn_fails'")
      db.log(c, name, "spawn", nil, "auto #" .. d(task.id))
      members[#members + 1] = { name = name }
      bo_name, bo_delay = nil, 0  -- the retry took the name: later tasks this tick get fresh ones
    elseif type(e) == "table" and e.lost then  -- a peer claimed it between pool() and now
    elseif type(e) == "table" and e.exit then  -- launch failed; cmd_spawn already reopened the task
      local delay = bo_delay == 0 and 300 or math.min(bo_delay * 2, 3600)  -- 5 min, doubling, capped at 1 h
      c:exec("insert or replace into meta(k,v) values('spawn_backoff',?)", ("%d,%d,%s"):format(util.now() + delay, delay, name))
      if bo_delay == 0 then  -- one notice per failure streak
        msgs.post(c, "swarm", comms, ("auto-spawn of %s for #%s failed: %s. Auto-spawn pauses %d min and retries, doubling."):format(
          name, d(task.id), M.launch_err or "launch error", math.floor(delay / 60)), false, "notice")
      end
      local f = c:one("select v from meta where k='spawn_fails'")
      local ft, fn = (f and f.v or ""):match("^(%d+),(%d+)$")
      fn = (ft == d(task.id) and tonumber(fn) or 0) + 1
      c:exec("insert or replace into meta(k,v) values('spawn_fails',?)", ("%s,%d"):format(d(task.id), fn))
      if fn >= M.SPAWN_FAILS then
        c:exec("insert or replace into meta(k,v) values('spawn_halt',?)", d(task.id))
        c:exec("delete from meta where k in ('spawn_backoff','spawn_fails')")
        msgs.post(c, "swarm", comms, ("auto-spawn for #%s failed %d times in a row (last: %s). Auto-spawn stops for it until it is claimed or changes; spawn it by hand."):format(
          d(task.id), fn, M.launch_err or "launch error"), true, "system")
      end
      break
    else
      error(e, 0)
    end
    ::next_task::
  end
end

M.SPAWN_FAILS = 5  -- failed launches in a row before auto-spawn gives up on a task

-- ---------- the tick ----------

function M.watchd_tick(c, comms, repo, opts)
  local terms = agents.hc_terminals()
  local live
  if terms ~= nil then
    live = {}
    for _, x in ipairs(terms) do
      if x.state == "live" and x.address then live[x.address] = true end
    end
  end
  M.reap(c, live, nil, comms)
  local t = util.now()
  if terms and #terms > 0 then
    local by = {}
    for _, x in ipairs(terms) do
      if x.address then by[x.address] = x end
    end
    for _, a in ipairs(agents.live_agents(c)) do
      local x = a.hc and by[a.hc]
      if x and x.status ~= "blocked" then  -- the prompt is gone: give back the claim hc blocked
        c:exec("update task set state='claimed', question=null, lease_until=? where owner=? and state='blocked' and question=?",
          t + M.LEASE, a.name, M.HC_Q)
      end
      if x and x.status == "blocked" and a.status ~= "blocked" then
        c:exec("update agent set status='blocked' where name=?", a.name)
        db.log(c, a.name, "blocked")
        local t_ = c:one("select id from task where owner=? and state='claimed' order by id limit 1", a.name)
        if t_ then  -- the agent notice below is the single notice; the task notice is marked sent
          c:exec("update task set state='blocked', question=? where id=?", M.HC_Q, t_.id)
          db.log(c, a.name, "task-blocked", d(t_.id), M.HC_Q)
        end
        if comms then
          msgs.post(c, "swarm", comms, a.name .. " is blocked (a prompt or question needs the human).", true, "system")
        end
      end
    end
  end
  if comms then  -- once per block: the event records that the question went out
    for _, r in ipairs(c:all("select * from task where state='blocked'")) do
      if not c:one("select 1 from event where kind='task-blocked' and path=? and data=?", d(r.id), r.question) then
        db.log(c, r.owner, "task-blocked", d(r.id), r.question)
        msgs.post(c, "swarm", comms, ("%s is blocked on #%s (%s): %s Answer with `swarm task unblock %s --answer \"...\"`."):format(
          r.owner or "None", d(r.id), r.title, r.question or "None", d(r.id)), true, "system")
      end
    end
  end
  conflict.conflict_tick(c, t)
  if comms then  -- without a communicator there is nobody to exempt from ending
    M.lifecycle(c, t, comms, terms, opts or {})
  end
  M.machine_tick(c)
  run.remote_tick(c, t)
  if repo then
    ci.ci_poll(c, repo)
    ci.ci_check(c, repo, comms)
    ci.pr_ci(c, repo)
  end
end

function M.last_event(c, ...)
  local kinds = { ... }
  local q = {}
  for i = 1, #kinds do q[i] = "?" end
  local r = c:one(("select kind from event where kind in (%s) order by id desc limit 1"):format(table.concat(q, ",")), ...)
  return r and r.kind
end

-- Edge-triggered pressure notice, heavy-count log, oom bias for agents' builds, orphan kills.
function M.machine_tick(c)
  local avail, total, psi = machine.mem_psi()
  if not avail then return end
  local procs = machine.read_procs()
  local hv = machine.heavy_procs(c, procs)
  local prev = c:one("select data from event where kind='heavy-count' order by id desc limit 1")
  if d(#hv) ~= (prev and prev.data or "0") then db.log(c, nil, "heavy-count", nil, d(#hv)) end
  for _, h in ipairs(hv) do  -- hygiene that rations nothing: the OOM killer picks agents' builds before the dev db and Claude
    if h.agent ~= "other session" then
      local f = machine.PROC .. "/" .. d(h.pid) .. "/oom_score_adj"
      local v = tonumber(util.strip(util.slurp(f) or "x"))
      if v and v < 500 then
        local w = io.open(f, "w")
        if w then w:write("500"); w:close() end
      end
    end
  end
  local high, was = machine.pressure_high(avail, total, psi), M.last_event(c, "pressure", "pressure-end") == "pressure"
  if high and not was then
    local ps = {}
    for _, p in pairs(procs) do ps[#ps + 1] = p end
    table.sort(ps, function(x, y)
      if x.rss_kb ~= y.rss_kb then return x.rss_kb > y.rss_kb end
      return x.pid < y.pid
    end)
    local top = {}
    for i = 1, math.min(3, #ps) do
      top[i] = ("%s(%s) %.1fG"):format(ps[i].comm, d(ps[i].pid), ps[i].rss_kb / 1048576)
    end
    local line = machine.machine_line(avail, total, psi)
    db.log(c, nil, "pressure", nil, line)
    local who, seen = {}, {}
    for _, h in ipairs(hv) do
      if h.agent ~= "other session" and not seen[h.agent] then seen[h.agent] = true; who[#who + 1] = h.agent end
    end
    table.sort(who)
    for _, w in ipairs(who) do
      msgs.post(c, "swarm", w, ("memory pressure: %s. Top holders: %s. Prefer other work or ask the agent holding the most."):format(
        line, table.concat(top, ", ")), false, "notice")
    end
  elseif was and not high then
    db.log(c, nil, "pressure-end")
  end
  -- orphans: heavy processes reparented to init whose cwd is in an ended agent's worktree and no live agent's
  local tops, order = {}, {}
  for _, r in ipairs(c:all("select name,cwd,ended from agent where cwd is not null")) do
    local k = isdir(r.cwd) and proc.git({ "rev-parse", "--show-toplevel" }, r.cwd) or false
    if not tops[k] then tops[k] = {}; order[#order + 1] = k end
    table.insert(tops[k], r)
  end
  local live_tops = {}
  for _, k in ipairs(order) do
    for _, x in ipairs(tops[k]) do
      if x.ended == nil then live_tops[k] = true end
    end
  end
  for _, h in ipairs(hv) do
    local l = h.ppid == 1 and unistd.readlink(machine.PROC .. "/" .. d(h.pid) .. "/cwd")
    if l then
      local cwd = realpath(l)
      for _, k in ipairs(order) do
        if nz(k) and not live_tops[k] and M.inside(cwd, k) then
          local kill = { h.pid }
          for _, q in pairs(procs) do
            if q.ppid == h.pid then kill[#kill + 1] = q.pid end
          end
          for _, pid in ipairs(kill) do signal.kill(pid, signal.SIGTERM) end
          db.log(c, tops[k][1].name, "orphan-kill", nil, ("%s %s %dM"):format(d(h.pid), util.cut(h.cmd, 60), math.floor(h.rss_kb / 1024)))
          break
        end
      end
    end
  end
end

-- ---------- commands ----------

function M.cmd_watchd(c, a)
  if a.dry_run then
    for _, x in ipairs(M.sweep_worktrees(c, nil, true)) do
      print(("%s\t%s\t%d MB"):format(x[1], x[2] or "None", x[3]))
    end
    return
  end
  local repo = a.ci and proc.git({ "rev-parse", "--show-toplevel" }) or nil
  local comms = nz(a.comms) or agents.env("SWARM_COMMS")
  local mine = d(unistd.getpid()) .. " " .. (agents.env("HC_TERMINAL_ID") or "-")  -- sw-ownership §4.6: the watchd record
  c:tx(function()
    local old = c:one("select v from meta where k='watchd'")
    local pid, term
    if old then pid, term = old.v:match("^(%S+)%s*(%S*)") end
    if old and old.v ~= mine and run.pid_alive(pid) and not a.takeover then
      util.die(("watchd already runs (pid %s, terminal %s); `swarm watchd --takeover` replaces it."):format(pid, term))
    end
    c:exec("insert or replace into meta(k,v) values('watchd',?)", mine)
    if comms then c:exec("insert or replace into meta(k,v) values('comms',?)", comms) end
  end)
  -- default cap: the roster the human launched, so watchd refills it but doesn't grow it
  local cap = a.max_agents
  if cap == nil then
    cap = 0
    for _, x in ipairs(agents.live_agents(c)) do
      if x.name ~= comms then cap = cap + 1 end
    end
  end
  local opts = { max_agents = cap, min_free_gib = a.min_free_mem, model = a.model, effort = a.effort, interval = a.interval }
  while true do
    local cur = c:one("select v from meta where k='watchd'")
    if not cur or cur.v ~= mine then
      util.die(("watchd (pid %s) was replaced by %s; exiting"):format(d(unistd.getpid()), cur and cur.v or "none"))
    end
    M.watchd_tick(c, comms, repo, opts)
    if a.once then return end
    io.stdout:flush()
    unistd.sleep(a.interval)
  end
end

function M.cmd_spawn(c, a)
  local name, tid = a.name, a.task_id
  local task = table.concat(a.task or {}, " ")
  local r
  if tid then
    r = tasks.reserve(c, name, tid, a.model)
    if task == "" then
      task = ("Board task #%s: %s. It is claimed for you; read its body with `swarm task show %s`."):format(d(tid), r.title, d(tid))
    end
  end
  if task == "" then util.die("usage: swarm spawn <name> [--model M] [--effort E] [--task N] -- <task>") end
  local here = os.getenv("SWARM_HERE")
  local self_ = util.join(here, "swarm")
  local dbp = db.dbpath()
  local tpl = util.slurp(util.join(here, "settings.template.json")) or util.die("no settings.template.json in " .. here)
  local sd = util.join(util.dirname(dbp), "agents")
  makedirs(sd)
  local sf = util.join(sd, name .. ".settings.json")
  local bindir = util.join(util.dirname(dbp), "bin")  -- puts `swarm` on the agent's PATH
  makedirs(bindir)
  if not pstat.lstat(util.join(bindir, "swarm")) then unistd.link(self_, util.join(bindir, "swarm"), true) end
  local f = io.open(sf, "w") or util.die("can't write " .. sf)
  f:write(replace(replace(replace(replace(tpl, "{{SWARM}}", self_), "{{DB}}", dbp), "{{NAME}}", name),
    "{{PATH}}", bindir .. ":" .. (os.getenv("PATH") or "")))
  f:close()
  local roster = {}
  for _, x in ipairs((agents.split_agents(c))) do roster[#roster + 1] = ("%s (%s)"):format(x.name, x.status or "None") end
  local brief = (util.slurp(util.join(here, "brief.md")) or "")
    .. ("\n\n---\nYour name: %s. Roster: %s.\nYour area and first task:\n%s\n"):format(
      name, #roster > 0 and table.concat(roster, ", ") or "nobody yet", task)
  local rules = c:one("select v from meta where k='rules'")
  if rules then brief = brief .. ("\nRules for this repo, from the communicator:\n%s\n"):format(rules.v or "None") end
  local launch = agents.env("SWARM_LAUNCH") or util.join(here, "..", "relaunch", "launch.sh")  -- tests point this at a fake
  local argv = { launch, name, "tab", brief, "--permission-mode", "auto", "--model", a.model, "--settings", sf }
  if a.effort then argv[#argv + 1] = "--effort"; argv[#argv + 1] = a.effort end
  local out, err, code = proc.exec(argv)
  if code ~= 0 then out = nil end
  M.launch_err = (util.strip(err or ""):gsub("\n.*", ""))  -- launch.sh's reason, for the watchd notice
  if out == nil then  -- launch.sh can fail after hc started the agent: keep a live terminal by that name
    for _, x in ipairs(agents.hc_terminals() or {}) do
      if x.name == name and x.state == "live" and x.address then out = x.address; break end
    end
  end
  if out == nil then
    if tid then tasks.unreserve(c, name, r) end
    util.die("launch.sh failed")
  end
  local lines = util.splitlines(util.strip(out))
  local addr = lines[#lines]
  if tid then
    c:exec("update agent set hc=? where name=? and hc is null", addr, name)
  else  -- shortcut: without --task nothing reserved the name, so a live one is overwritten; reserve here too if it bites
    agents.bind(c, name, unistd.getcwd(), addr, a.model, true)
  end
  db.log(c, agents.env("SWARM_NAME") and agents.me() or "human", "spawn", nil, name)
  print(("spawned %s at %s"):format(name, util.strip(out)))
end

return M
