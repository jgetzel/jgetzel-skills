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
    if o and o.ended == nil and o.status == "idle" and not bg then bg = machine.bg_agents(c, machine.procs()) end
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
    if not c:one([[select 1 from agent where name=? and ended is null and status='idle' and hc is ? and stay is null
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
  local kb = machine.mem()
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
  local pcwd, cw = {}, machine.cwds()
  if not cw then return {} end  -- which worktrees a process sits in is unknown, so sweep none
  for _, l in pairs(cw) do pcwd[#pcwd + 1] = realpath(l) end
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

M.UNCLEAN_IDLE = 1800  -- an idle agent kept only by its unclean worktree this long (s) is told what holds it

-- What keeps worktree wt from landing: git status lines and commits not on B.
function M.unclean_list(wt, B)
  if not exists(wt) then return wt .. " is gone; its branch holds commits not on " .. B end
  local l = {}
  for _, s in ipairs(util.splitlines(proc.run({ "git", "-C", wt, "status", "--porcelain" }) or "")) do
    if s ~= "" then l[#l + 1] = s end
  end
  for _, s in ipairs(util.splitlines(proc.run({ "git", "-C", wt, "log", "--oneline", B .. "..HEAD" }) or "")) do
    if s ~= "" then l[#l + 1] = "commit " .. s end
  end
  return table.concat(l, "\n")
end

-- Agent a is idle and kept only by its unclean worktree wt. Once per idle stretch and per list (edge-triggered, as
-- the digest is): wake it with the list; if it is idle again with the same list, or has no live waiter, tell comms.
function M.unclean(c, a, wt, B, t, comms)
  local n, since = a.name, a.last_active or 0
  if t - since < M.UNCLEAN_IDLE then return end
  local last = c:one("select ts, kind, data from event where agent=? and kind in ('unclean-nudge','unclean-notice') order by id desc limit 1", n)
  if last and last.ts >= since then return end  -- already handled this idle stretch
  local list = M.unclean_list(wt, B)
  local same = last and last.data == list
  if same and last.kind == "unclean-notice" then return end
  local ls = util.splitlines(list)
  local shown = table.concat(ls, "\n", 1, math.min(20, #ls)) .. (#ls > 20 and ("\n+%d more"):format(#ls - 20) or "")
  local mins = math.floor((t - since) / 60)
  if not same and a.waiter and signal.kill(a.waiter, 0) == 0 then
    db.log(c, n, "unclean-nudge", wt, list)
    msgs.post(c, "swarm", n, ("You are idle %d min with no claim or lock; watchd keeps you only because worktree %s holds:\n%s\n"
      .. "If your work is done: land what is real, delete or ignore build outputs and scratch, then stop, and watchd ends you. "
      .. "If not, tell the communicator (%s) what you are waiting on."):format(mins, wt, shown, comms), true, "system")
  else
    db.log(c, n, "unclean-notice", wt, list)
    msgs.post(c, "swarm", comms, ("%s is idle %d min, kept only by its unclean worktree %s (%s):\n%s"):format(
      n, mins, wt, same and "nudged once, idle again and still unclean" or "no live waiter, so not nudged", shown), false, "system")
  end
end

-- The swarm is quiet when no task is open, claimed or blocked and only stayers and comms are live. On the edge into
-- quiet (re-armed by the next task add or claim) each wakeable stayer is asked once whether its stay is over, and comms
-- gets one notice naming the stayers: the "all tasks done" signal (sw-roles §4).
function M.quiet(c, t, comms)
  if c:one("select 1 from task where state in ('open','claimed','blocked')") then return end
  local q = c:one("select id from event where kind='quiet' order by id desc limit 1")
  if not c:one("select 1 from event where kind in ('task-add','claim') and id>?", q and q.id or 0) then return end
  local stayers = {}
  for _, a in ipairs(agents.live_agents(c)) do
    if a.name ~= comms and not agents.is_comms(c, a.name) then
      if not nz(a.stay) then return end  -- someone is still working
      stayers[#stayers + 1] = a
    end
  end
  db.log(c, nil, "quiet", nil, d(#stayers))
  local l = {}
  for _, a in ipairs(stayers) do
    local waits = a.waiter and signal.kill(a.waiter, 0) == 0
    local woken = waits and not agents.cold_reason(a, t)
    if woken then
      msgs.post(c, "swarm", a.name, ("The board is empty and nobody is working. You stay for: '%s'. If that is over, "
        .. "`swarm stay --end` and stop; if not, carry on."):format(a.stay), false, "system")
    end
    l[#l + 1] = ("%s%s stays for '%s' (%s)"):format(a.name, nz(a.role) and " " .. a.role or "", a.stay,
      woken and "asked if that is over" or waits and "cold, not woken" or "no live waiter, not woken")
  end
  msgs.post(c, "swarm", comms, "The swarm is quiet: no task is open, claimed or blocked and nobody else is working. "
    .. (#l > 0 and "Stayers:\n" .. table.concat(l, "\n") or "No stayers.") .. "\nIf the work is done, tell the user.", false, "system")
end

M.LIVENESS_IDLE = 50 * 60  -- a stayer idle this long (inside the 1 h cache) is asked if it still stays
M.LIVENESS_WAIT = 5 * 60   -- and is hung if its last_active has not moved this long after

-- Hung stayers (sw-roles §4): two edge notices (no live waiter; a message unread two ticks) and the one periodic
-- check. All state is in events newer than the stayer's last_active, so any wake re-arms everything.
function M.hung(c, t, comms, terms, opts)
  local tick = (opts and opts.interval) or 30
  for _, a in ipairs(agents.live_agents(c)) do
    local n, last = a.name, a.last_active or 0
    if n ~= comms and not agents.is_comms(c, n) and nz(a.stay) and a.status == "idle" then
      local function ev(kind, data)
        return c:one("select ts from event where agent=? and kind=? and ts>=? and (? is null or data=?) order by id desc limit 1",
          n, kind, last, data, data)
      end
      if not (a.waiter and signal.kill(a.waiter, 0) == 0) then
        if not ev("stay-nowaiter") then
          db.log(c, n, "stay-nowaiter")
          msgs.post(c, "swarm", comms, ("%s stays for '%s' but has no waiter and can't be woken."):format(n, a.stay), false, "system")
        end
      else
        for _, m in ipairs(msgs.unread(c, n)) do
          if m.dest == n and m.ts <= t - 2 * tick and not m.body:find("^Liveness check:") and not ev("stay-unwoken", d(m.id)) then
            db.log(c, n, "stay-unwoken", nil, d(m.id))
            msgs.post(c, "swarm", comms, ("%s did not wake on a message (#%s from %s, %d s ago)."):format(
              n, d(m.id), m.frm, t - m.ts), false, "system")
          end
        end
        local chk = ev("stay-check")
        if ev("stay-hung") then  -- no more checks until it is active again
        elseif chk then
          if t - chk.ts >= M.LIVENESS_WAIT then
            local x
            for _, y in ipairs(terms or {}) do if y.address == a.hc then x = y end end
            db.log(c, n, "stay-hung")
            msgs.post(c, "swarm", comms, ("%s stays for '%s' and did not answer the liveness check (terminal %s, hc status %s). "
              .. "Unstick it with `hc send`, or end it."):format(n, a.stay, a.hc or "?", x and x.status or "unknown"), true, "system")
          end
        elseif t - last >= M.LIVENESS_IDLE and not agents.cold_reason(a, t) then  -- a cold wake resends the whole context
          db.log(c, n, "stay-check")
          msgs.post(c, "swarm", n, ("Liveness check: you have stayed %d min for '%s'. If that still holds, do nothing. "
            .. "If it is over, `swarm stay --end`."):format(math.floor((t - last) / 60), a.stay), false, "system")
        end
      end
    end
  end
end

-- End finished agents, digest reusable ones, spawn fresh ones for startable tasks (sw-lifecycle §4).
function M.lifecycle(c, t, comms, terms, opts)
  local wts, all_wts = conflict.wt_map(c), conflict.worktrees()
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
  local function unlanded(n)  -- a worktree n owns that holds work not on B, not just the one wt_map picked
    local own = conflict.owned_wts(n, all_wts)
    if wts[n] then table.insert(own, 1, wts[n]) end
    for _, w in ipairs(own) do
      if not M.landed(w, B, main) then return w end
    end
  end
  local function ours(cwd)  -- in this repo or one of its worktrees: else another swarm's terminal (#117)
    cwd = realpath(cwd)
    for _, w in ipairs(all_wts) do
      if cwd == w[1] or util.startswith(cwd, w[1] .. "/") then return true end
    end
    return main ~= nil and (cwd == main or util.startswith(cwd, main .. "/"))
  end
  local reusable = {}
  for _, a in ipairs(agents.live_agents(c)) do
    local n = a.name
    local x = nz(a.hc) and terms ~= nil and by[a.hc] or nil
    if not (nz(a.stay) or a.status ~= "idle" or t - (a.last_active or 0) < 120 or (x and nz(x.cwd) and not ours(x.cwd))
        or (nz(a.hc) and terms ~= nil and (not x or (x.status ~= "idle" and x.status ~= "done")))
        or c:one("select 1 from task where owner=? and state in ('claimed','blocked')", n)
        or c:one("select 1 from lock where agent=?", n)) then
      local held = unlanded(n)
      if held then
        M.unclean(c, a, held, B, t, comms)
      -- one that passed the work over, or whose waiter is gone (never wakes on a digest), is ended,
      -- not kept as a reason to spawn no one
      elseif (a.ctx_tokens or 0) < agents.SMALL_CTX and #pool > 0 and not passed_over(n)
          and a.waiter and signal.kill(a.waiter, 0) == 0 then
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
  local held = #reusable == 0 and #pool > 0 and M.auto_spawn(c, comms, opts, pool) or nil
  local old = c:one("select v from meta where k='spawn_held'")
  if held then
    c:exec("insert or replace into meta(k,v) values('spawn_held',?)", held)
    if not old then db.log(c, "swarm", "spawn-held", nil, held) end  -- one per edge; the board shows it while it holds
  elseif old then
    c:exec("delete from meta where k='spawn_held'")
  end
end

-- Staff startable tasks up to the auto-spawn number; returns the board's "auto-spawn holding" line when a limit
-- stops it, else nil.
function M.auto_spawn(c, comms, opts, pool)
  local _, mn, mx = agents.limits(c)
  if not mn then return end
  local members = {}
  for _, a in ipairs(agents.live_agents(c)) do
    if a.name ~= comms then
      members[#members + 1] = a
    end
  end
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
  local function startable(k)  -- tasks auto-spawn would still staff, from pool[k] on
    local n = 0
    for j = k, #pool do if not (halt and tostring(pool[j].id) == halt.v) then n = n + 1 end end
    return n
  end
  for k, task in ipairs(pool) do
    if halt and tostring(task.id) == halt.v then goto next_task end
    if #members >= mn then
      return ("auto-spawn holding: %d live, the auto-spawn number is %d; %d task(s) startable%s"):format(
        #members, mn, startable(k), mx and "; max " .. mx or "")
    end
    local free, want = M.mem_available_gib(), opts.min_free_gib or 4
    if free < want then
      return ("auto-spawn holding: %.1fG free, wants %gG; %d task(s) startable"):format(free, want, startable(k))
    end
    local name = nz(bo_name)
    if not name then top = top + 1; name = prefix .. d(top) end
    local model = nz(task.model) or nz(opts.model) or "sonnet"
    local ok, e = pcall(M.cmd_spawn, c, { name = name, model = model, effort = nz(task.effort) or nz(opts.effort), task_id = task.id, task = {} })
    if ok then
      c:exec("delete from meta where k='spawn_backoff'")
      c:exec("delete from meta where k='spawn_fails'")
      db.log(c, name, "spawn", nil, "auto #" .. d(task.id))
      members[#members + 1] = { name = name }
      bo_name, bo_delay = nil, 0  -- the retry took the name: later tasks this tick get fresh ones
    elseif type(e) == "table" and e.lost then  -- a peer claimed it between pool() and now
    elseif type(e) == "table" and e.refused then  -- an agent spawned between limits() and now: the max holds
      return ("auto-spawn holding: %s; %d task(s) startable"):format(e.refused:match("^[^.]*"), startable(k))
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
  if comms then  -- ending reports to the communicator; without one, nobody hears what it did
    M.lifecycle(c, t, comms, terms, opts or {})
    M.quiet(c, t, comms)
    M.hung(c, t, comms, terms, opts)
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
  local avail, total, psi = machine.mem()
  if not avail then return end
  local procs = machine.procs()
  local hv = machine.heavy_procs(c, procs)
  local prev = c:one("select data from event where kind='heavy-count' order by id desc limit 1")
  if d(#hv) ~= (prev and prev.data or "0") then db.log(c, nil, "heavy-count", nil, d(#hv)) end
  for _, h in ipairs(hv) do  -- hygiene that rations nothing: the OOM killer picks agents' builds before the dev db and Claude
    if h.agent ~= "other session" and machine.OS == "Linux" then  -- macOS has no unprivileged per-process knob
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
    table.sort(hv, function(x, y)
      if x.rss_kb ~= y.rss_kb then return x.rss_kb > y.rss_kb end
      return x.pid < y.pid
    end)
    for _, h in ipairs(hv) do  -- the three agents holding the most memory, then every stayer
      if h.agent ~= "other session" and not seen[h.agent] and #who < 3 then seen[h.agent] = true; who[#who + 1] = h.agent end
    end
    for _, s in ipairs(c:all("select name from agent where ended is null and stay is not null")) do
      if not seen[s.name] then seen[s.name] = true; who[#who + 1] = s.name end
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
  local cw
  for _, h in ipairs(hv) do
    if h.ppid == 1 then cw = cw or machine.cwds() or {} end
    local l = h.ppid == 1 and cw[h.pid]
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
    if comms then  -- the communicator is a stayer; meta.comms is only where watchd sends what needs the human
      c:exec("insert or replace into meta(k,v) values('comms',?)", comms)
      if c:exec("update agent set stay=? where name=? and ended is null and stay is null", "the user's channel", comms) > 0 then
        db.log(c, comms, "stay", nil, "the user's channel")
      end
    end
  end)
  -- the auto-spawn number (sw-roles §6): --max-agents writes it (deprecated: `swarm limits --min`); else the first
  -- watchd sets it to the roster the human launched, so watchd refills it but doesn't grow it
  local live, mn = agents.limits(c)
  if a.max_agents or not mn then
    c:exec("insert or replace into meta(k,v) values('agent_min',?)", d(a.max_agents or live))
  end
  local opts = { min_free_gib = a.min_free_mem, model = a.model, effort = a.effort, interval = a.interval }
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
  if not tid and task == "" then
    util.die("usage: swarm spawn <name> [--model M] [--effort E] [--role R] [--stay S] [--task N] -- <task>")
  end
  local spawner = agents.env("SWARM_NAME") and agents.me() or "human"
  local ok, r = pcall(function() return tid and tasks.reserve(c, name, tid, a.model) or agents.reserve(c, name, a.model) end)
  if not ok then
    if type(r) == "table" and r.refused then db.log(c, spawner, "spawn-refused", nil, name) end
    error(r, 0)
  end
  if a.role then agents.set_role(c, name, a.role) end
  if a.stay then c:exec("update agent set stay=? where name=?", agents.one_line(a.stay), name) end  -- a stayer before its first turn
  if tid and task == "" then
    task = ("Board task #%s: %s. It is claimed for you; read its body with `swarm task show %s`."):format(d(tid), r.title, d(tid))
  end
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
  for _, x in ipairs((agents.split_agents(c))) do
    roster[#roster + 1] = ("%s (%s%s)"):format(x.name, x.status or "None", x.role and (", " .. x.role) or "")
  end
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
    tasks.unreserve(c, name, tid and r or nil)
    util.die("launch.sh failed")
  end
  local lines = util.splitlines(util.strip(out))
  local addr = lines[#lines]
  c:exec("update agent set hc=? where name=? and hc is null", addr, name)
  db.log(c, spawner, "spawn", nil, name)
  print(("spawned %s at %s"):format(name, util.strip(out)))
  print(machine.machine_note(c, name))  -- the cost of the next agent (live and launched counts come with the limits)
end

return M
