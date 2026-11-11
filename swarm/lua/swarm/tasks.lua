-- The board: task timing, deps (after/blocks, cycles), the pool of ready work, reserve for spawn; cmd task/board/rules.
local util, db = require "swarm.util", require "swarm.db"
local agents, hook = require "swarm.agents", require "swarm.hook"
local unistd = require "posix.unistd"
local M = {}

M.LEASE = 7200
M.RED_TASK = "main red: "  -- a red main is one board task, so one agent fixes it; watchd closes it on the next green
M.TASK_KINDS = { "task-add", "claim", "spawn", "done", "block", "unblock", "release", "drop" }

local function py(x)  -- Python truthiness for a db value: NULL, 0 and '' are false
  if x == nil or x == 0 or x == "" or x == false then return nil end
  return x
end

local function d(n) return util.d(n) end

-- Task id an event is about: data starts '#<id>' (spawn: 'auto #<id>'), else nil.
function M.event_task(e)
  local s = e.data or ""
  local id, rest = s:match("^#(%d+)(.*)$")
  if not id then id, rest = s:match("^auto #(%d+)(.*)$") end
  if id and (rest == "" or rest:sub(1, 1) == " ") then return tonumber(id) end
  return nil
end

-- Task durations (seconds) from the CLI-written columns, else from the task's claim/done/block/unblock/release/drop
-- events (evs: that task's events in order). Mirrors swarm-retro/swarm-report's task timing.
function M.task_timing(r, evs)
  local function ts(k, agg)
    local v
    for _, e in ipairs(evs) do
      local kind = e.kind == "spawn" and "claim" or e.kind  -- watchd's auto-spawn claims with a 'spawn' event
      if kind == k then v = v and agg(v, e.ts) or e.ts end
    end
    return v
  end
  local claims, holders, seen, releases = 0, {}, {}, 0
  for _, e in ipairs(evs) do
    if e.kind == "claim" or e.kind == "spawn" then
      claims = claims + 1
      if not seen[e.agent] then seen[e.agent] = true; holders[#holders + 1] = e.agent end
    elseif e.kind == "release" then
      releases = releases + 1
    end
  end
  local created = py(r.created_at) or ts("task-add", math.min)
  local first = py(r.first_claimed_at) or ts("claim", math.min)
  local done = py(r.done_at) or (r.state == "done" and ts("done", math.max) or nil)
  local dropped = py(r.dropped_at) or (r.state == "dropped" and ts("drop", math.max) or nil)
  local stop = py(done) or py(dropped) or util.now()
  local blocked, start = 0, nil
  for _, e in ipairs(evs) do
    if e.kind == "block" and start == nil then start = e.ts
    elseif e.kind == "unblock" and start ~= nil then blocked, start = blocked + e.ts - start, nil end
  end
  if start ~= nil and r.state == "blocked" then blocked = blocked + stop - start end
  local function span(a, b) return a ~= nil and b ~= nil and b - a or nil end
  return { created_at = created, first_claimed_at = first, done_at = done, dropped_at = dropped,
    queue_wait_s = span(created, first), work_s = span(first, done), total_s = span(created, done), blocked_s = blocked,
    claims = claims, releases = releases, holders = holders, claim_ctx = r.claim_ctx, done_ctx = r.done_ctx,
    pr = r.pr, merged_at = r.merged_at, ci_conclusion = r.ci_conclusion,
    merge_to_green_s = span(r.merged_at, r.ci_green_at) }
end

function M.task_events(c, tid)
  local r = {}
  for _, e in ipairs(c:all("select ts,agent,kind,data from event where kind in ('" .. table.concat(M.TASK_KINDS, "','")
      .. "') order by id")) do
    if M.event_task(e) == tid then r[#r + 1] = e end
  end
  return r
end

-- The ids a task row waits on, in the order given.
function M.deps_of(r)
  local r2 = {}
  for x in (r.deps or ""):gmatch("[^,]+") do r2[#r2 + 1] = tonumber(x) end
  return r2
end

-- The rows of r's dependencies that aren't done, in r's order: what it waits on.
function M.undone(c, r)
  local deps, out = M.deps_of(r), {}
  if #deps == 0 then return out end
  local q = {}
  for i = 1, #deps do q[i] = "?" end
  local st = {}
  for _, x in ipairs(c:all("select * from task where id in (" .. table.concat(q, ",") .. ") and state!='done'", unpack(deps))) do
    st[x.id] = x
  end
  for _, i in ipairs(deps) do
    if st[i] then out[#out + 1] = st[i] end
  end
  return out
end

-- Open tasks whose deps contain #tid.
function M.waiters(c, tid)
  return c:all("select * from task where state='open' and ','||deps||',' like ?", "%," .. d(tid) .. ",%")
end

-- {start, …, target} along deps, or nil: the cycle `task after` would close.
function M.dep_path(c, start, target)
  local seen, stack = {}, { { start } }
  while #stack > 0 do
    local path = table.remove(stack)
    local last = path[#path]
    if last == target then return path end
    if not seen[last] then
      seen[last] = true
      local r = c:one("select * from task where id=?", last)
      local deps = r and M.deps_of(r) or {}
      for i = #deps, 1, -1 do
        local p = { unpack(path) }
        p[#p + 1] = deps[i]
        stack[#stack + 1] = p
      end
    end
  end
  return nil
end

-- Open tasks whose --after dependencies are all done: work that can start.
function M.pool(c)
  return c:all("select * from task t where state='open' and not exists (select 1 from task d where d.state!='done' "
    .. "and ','||t.deps||',' like '%,'||d.id||',%') order by title like ? desc, id", M.RED_TASK .. "%")
end

-- task show's after: and blocks: lines.
function M.dep_lines(c, r)
  local st = {}
  for _, x in ipairs(c:all("select id,state from task")) do st[x.id] = x.state end
  local deps, out = M.deps_of(r), ""
  if #deps > 0 then
    local p = {}
    for i, x in ipairs(deps) do p[i] = "#" .. d(x) .. " " .. (st[x] or "missing") end
    out = "\nafter: " .. table.concat(p, ", ")
  end
  local w = r.state ~= "done" and M.waiters(c, r.id) or {}
  if #w > 0 then
    local p = {}
    for i, x in ipairs(w) do p[i] = "#" .. d(x.id) end
    out = out .. "\nblocks: " .. table.concat(p, ", ")
  end
  return out
end

local function ids(rows, f)
  local p = {}
  for i, x in ipairs(rows) do p[i] = f and f(x) or "#" .. d(x) end
  return table.concat(p, ", ")
end

local function no_task_to_wait_on(c, deps)
  for _, x in ipairs(deps) do
    if not c:one("select 1 from task where id=?", x) then util.die(("no task #%s to wait on"):format(d(x))) end
  end
end

-- Refuse a missing dep or a cycle, then store the list; returns it as strings.
function M.set_deps(c, id, deps)
  local ds = {}
  for i, x in ipairs(deps) do
    no_task_to_wait_on(c, { x })
    local cyc = M.dep_path(c, x, id)
    if cyc then
      table.insert(cyc, 1, id)
      local p = {}
      for j, y in ipairs(cyc) do p[j] = "#" .. d(y) end
      util.die("that would be a cycle: " .. table.concat(p, " → "))
    end
    ds[i] = d(x)
  end
  c:exec("update task set deps=? where id=?", table.concat(ds, ","), id)
  return ds
end

local function ctx_of(c, n)
  local r = c:one("select ctx_tokens from agent where name=?", n)
  return r and r.ctx_tokens or 0
end

-- reap took task id from n and nobody has claimed it since: retaking it is n's own work, not new work
local function reaped_from(c, n, id)
  local last
  for _, e in ipairs(M.task_events(c, id)) do
    if e.kind == "claim" or e.kind == "spawn" then last = e.agent end
  end
  return last == n
    and c:one("select 1 from event where kind='reap' and agent=? and data=?", n, ("task #%s lease expired"):format(d(id))) ~= nil
end

local function owned(r)  -- `, owned by x` when the row has an owner
  return py(r.owner) and (", owned by " .. r.owner) or ""
end

function M.cmd_task(c, a)
  local n = agents.me()
  local t = util.now()
  if a.act == "add" then
    local deps = a.after or {}
    local id = c:tx(function()
      no_task_to_wait_on(c, deps)
      local ds = {}
      for i, x in ipairs(deps) do ds[i] = d(x) end
      c:exec("insert into task(title,body,created_by,deps,model,effort,base,created_at) values(?,?,?,?,?,?,?,?)",
        a.title, a.body, n, py(table.concat(ds, ",")), a.model, a.effort, a.base, t)
      local id = c:last_id()
      db.log(c, n, "task-add", nil, ("#%s %s"):format(d(id), a.title))
      return id
    end)
    print("task #" .. d(id))
    return
  end
  local r = c:one("select * from task where id=?", a.id)
  if not r then util.die("no task #" .. d(a.id)) end
  local mine = " where id=? and owner=? and state='claimed'"  -- owner and state checked in the write (sw-ownership §3.2)

  if a.act == "claim" then
    local dep = M.undone(c, r)[1]
    if dep then
      util.die(("#%s waits on #%s (%s%s)"):format(d(a.id), d(dep.id), dep.state,
        py(dep.owner) and (", claimed by " .. dep.owner) or ""))
    end
    agents.touch(c, n)
    local k = ctx_of(c, n)
    if k >= hook.CTX_WARN and not reaped_from(c, n, a.id) then
      util.die(("context ~%dk, too high to take new work: %s"):format(math.floor(k / 1000), hook.ctx_advice(k)))
    end
    local until_ = t + util.dur(a.lease)
    -- the deps are checked again in the write: a `task after` since the check above must hold it back
    if c:exec("update task set state='claimed', owner=?, lease_until=?, claim_ctx=?, "
        .. "first_claimed_at=coalesce(first_claimed_at,?) where id=? and state='open' and not exists "
        .. "(select 1 from task d where d.state!='done' and ','||task.deps||',' like '%,'||d.id||',%')",
        n, until_, k, t, a.id) == 0 then
      local r2 = c:one("select * from task where id=?", a.id)
      local dep2 = r2.state == "open" and M.undone(c, r2)[1]
      if dep2 then util.die(("#%s waits on #%s (%s)"):format(d(a.id), d(dep2.id), dep2.state)) end
      util.die(("task #%s is %s%s"):format(d(a.id), r2.state, owned(r2)))
    end
    db.log(c, n, "claim", nil, ("#%s %s"):format(d(a.id), r.title))
    print(("claimed #%s until %s"):format(d(a.id), util.hhmm(until_)))
    local machine = require "swarm.machine"
    local avail, total, psi = machine.mem()
    if avail then  -- the line; the full note when pressure is high
      print(machine.pressure_high(avail, total, psi) and machine.machine_note(c, n) or machine.machine_line(avail, total, psi))
    end
    print(py(r.body) or "(no body)")

  elseif a.act == "show" then
    local tm = M.task_timing(r, M.task_events(c, r.id))
    local function f(k) return tm[k] ~= nil and ("%dm"):format(math.floor(tm[k] / 60)) or "-" end
    local s = ("#%s %s %s  %s\ntiming: queue %s, work %s, total %s, blocked %s, claims %d, releases %d, held by %s"):format(
      d(r.id), r.state, py(r.owner) or "-", r.title, f("queue_wait_s"), f("work_s"), f("total_s"), f("blocked_s"),
      tm.claims, tm.releases, py(table.concat(tm.holders, ", ")) or "-")
    if py(r.base) then s = s .. "\nbase: " .. r.base end
    if py(tm.claim_ctx) then s = s .. (", ctx %dk at claim"):format(math.floor(tm.claim_ctx / 1000)) end
    if py(tm.done_ctx) then s = s .. (" -> %dk at done"):format(math.floor(tm.done_ctx / 1000)) end
    if py(tm.merged_at) then
      s = s .. ("\nPR #%s merged %s, main CI %s"):format(tm.pr and d(tm.pr) or "None", util.hhmm(tm.merged_at),
        py(tm.ci_conclusion) or "pending")
      if tm.merge_to_green_s ~= nil then
        s = s .. (", green %dm after merge"):format(math.floor(tm.merge_to_green_s / 60))
      end
    end
    print(s .. M.dep_lines(c, r) .. "\n" .. (py(r.body) or "(no body)")
      .. (py(r.answer) and "\nAnswer to the block: " .. r.answer or ""))

  elseif a.act == "after" then
    c:tx(function()
      local r2 = c:one("select * from task where id=?", a.id)
      if r2.state ~= "open" then
        util.die(("task #%s is %s; only an open task's dependencies can change"):format(d(a.id), r2.state))
      end
      local ds = M.set_deps(c, a.id, a.deps)
      db.log(c, n, "task-after", nil, ("#%s after %s"):format(d(a.id), py(table.concat(ds, ",")) or "-"))
    end)
    print(("#%s after %s"):format(d(a.id), py(ids(a.deps)) or "nothing"))

  elseif a.act == "renew" then
    local until_ = t + util.dur(a.lease)
    if c:exec("update task set lease_until=?" .. mine, until_, a.id, n) == 0 then
      util.die(("task #%s is not claimed by you"):format(d(a.id)))
    end
    print(("renewed #%s until %s"):format(d(a.id), util.hhmm(until_)))

  elseif a.act == "done" then
    if util.strip(a.evidence or "") == "" then
      util.die("--evidence is empty: give the sha, PR or command output that shows the work is done")
    end
    if util.startswith(r.title or "", M.RED_TASK) then  -- a run that predates the fix could still go red: green closes it
      if c:exec("update task set evidence=?" .. mine, a.evidence, a.id, n) == 0 then
        util.die(("task #%s is not claimed by you"):format(d(a.id)))
      end
      print(("#%s stays yours until a green run: watchd marks it done then, and you can go idle now."):format(d(a.id)))
      return
    end
    c:tx(function()
      if c:exec("update task set state='done', evidence=?, lease_until=null, done_at=?, "
          .. "done_ctx=(select ctx_tokens from agent where name=?)" .. mine, a.evidence, t, n, a.id, n) == 0 then
        util.die(("task #%s is not claimed by you"):format(d(a.id)))
      end
      db.log(c, n, "done", nil, ("#%s %s"):format(d(a.id), a.evidence))
    end)
    print("done #" .. d(a.id))
    local k, stay = math.floor(ctx_of(c, n) / 1000), agents.stay_of(c, n)
    if stay then
      print(("context ~%dk: you stay for '%s'. `swarm stay --end` when that is over."):format(k, stay))
    elseif k * 1000 < agents.SMALL_CTX and #M.pool(c) > 0 then
      print(("context ~%dk: take the next task (swarm board)."):format(k))
    else
      print(("context ~%dk: go idle. watchd ends you once your work lands; a fresh agent takes new work."):format(k))
    end

  elseif a.act == "block" then
    c:tx(function()
      if c:exec("update task set state='blocked', question=? where id=? and owner=? and state='claimed'",
          a.question, a.id, n) == 0 then
        util.die(("task #%s is not claimed by you"):format(d(a.id)))
      end
      db.log(c, n, "block", nil, ("#%s %s"):format(d(a.id), a.question))
    end)
    print(("blocked #%s; %s It stays yours until `swarm task unblock`."):format(d(a.id), agents.away(c)
      and "the user is away: park this and take work that doesn't need the answer." or "watchd tells the communicator."))

  elseif a.act == "unblock" then
    if r.state ~= "blocked" then util.die(("task #%s is not blocked"):format(d(a.id))) end
    if n ~= r.owner and not agents.in_charge(c, n) then
      util.die(("only %s or the communicator can unblock #%s"):format(tostring(r.owner), d(a.id)))
    end
    c:tx(function()
      if c:exec("update task set state='claimed', question=null, answer=coalesce(?, answer), lease_until=? where id=? and owner=? and state='blocked'",
          py(a.answer), t + M.LEASE, a.id, r.owner) == 0 then
        util.die(("task #%s changed under you; `swarm task show %s`"):format(d(a.id), d(a.id)))
      end
      db.log(c, n, "unblock", nil, "#" .. d(a.id))
      if py(a.answer) and n ~= r.owner then
        require("swarm.msgs").post(c, n, r.owner, ("#%s is unblocked. Answer: %s"):format(d(a.id), a.answer))
      end
    end)
    print(("unblocked #%s; claimed by %s again"):format(d(a.id), r.owner))

  elseif a.act == "release" then
    -- the user or the communicator may take back a task another holds, claimed or blocked; its ex-owner is told
    local from = r.owner ~= n and agents.in_charge(c, n) and py(r.owner)
    c:tx(function()
      if from then
        if c:exec("update task set state='open', owner=null, lease_until=null, question=null where id=? and owner=? "
            .. "and state in ('claimed','blocked')", a.id, from) == 0 then
          local r2 = c:one("select * from task where id=?", a.id)
          util.die(("task #%s is %s%s"):format(d(a.id), r2.state, owned(r2)))
        end
      elseif c:exec("update task set state='open', owner=null, lease_until=null where id=? and owner=? and state='claimed'",
          a.id, n) == 0 then
        util.die(("task #%s is not claimed by you"):format(d(a.id)))
      end
      if a.after then M.set_deps(c, a.id, a.after) end
      db.log(c, n, "release", nil, "#" .. d(a.id) .. (from and " from " .. from or ""))
      if from then
        require("swarm.msgs").post(c, n, from, ("%s released #%s: stop work on it"):format(
          n == agents.HUMAN and "the user" or n, d(a.id)), true)
      end
    end)
    print(("released #%s%s; it is open again%s"):format(d(a.id), from and (" from " .. from) or "",
      a.after and #a.after > 0 and (" after " .. ids(a.after)) or ""))

  elseif a.act == "drop" then
    c:tx(function()
      local r2 = c:one("select * from task where id=?", a.id)
      if (r2.state == "claimed" or r2.state == "blocked") and r2.owner ~= n and not agents.in_charge(c, n) then
        util.die(("#%s is %s by %s; only it or the communicator can drop it"):format(d(a.id), r2.state, tostring(r2.owner)))
      end
      c:exec("update task set state='dropped', owner=null, lease_until=null, dropped_at=? where id=?", t, a.id)
      db.log(c, n, "drop", nil, "#" .. d(a.id))
    end)
    print("dropped #" .. d(a.id))
    for _, w in ipairs(M.waiters(c, a.id)) do  -- information, not a rule: a dropped dependency still holds them back
      print(("#%s waits on #%s: drop it too, or `swarm task after %s …`"):format(d(w.id), d(a.id), d(w.id)))
    end
  end
end

function M.cmd_board(c, a)
  local machine = require "swarm.machine"
  local avail, total, psi = machine.mem()
  if avail then print(machine.machine_line(avail, total, psi)) end
  local role = {}
  for _, x in ipairs(c:all("select name, role from agent where ended is null and role is not null")) do role[x.name] = x.role end
  local rows = c:all("select * from task " .. (a.all and "" or "where state in ('open','claimed','blocked') ")
    .. "order by title like '" .. M.RED_TASK .. "%' and state!='done' desc, id")
  print(agents.limits_line(c))
  local held = c:one("select v from meta where k='spawn_held'")
  if held then print(held.v) end
  for _, r in ipairs(rows) do
    local who = (py(r.owner) or "-") .. (role[r.owner] and (" (" .. role[r.owner] .. ")") or "")
    if r.state == "blocked" then
      print(("#%s blocked by %s: %s  %s"):format(d(r.id), who, r.question or "None", r.title))
    else
      local lease = ""
      if r.state == "claimed" then
        local left = (r.lease_until or 0) - util.now()
        lease = left > 0 and (" lease %dm left"):format(math.floor(left / 60)) or " lease EXPIRED"
      end
      local u = M.undone(c, r)
      local wait = #u > 0 and (" after " .. ids(u, function(x)
        return "#" .. d(x.id) .. (x.state == "dropped" and " (dropped)" or "")
      end)) or ""
      print(("#%s %-7s %s%s%s  %s"):format(d(r.id), r.state, who, lease, wait, r.title)
        .. (py(r.body) and "  [body: task show]" or "")
        .. (py(r.evidence) and ("  [evidence: " .. r.evidence .. "]") or ""))
    end
  end
  if a.all then
    print(("(%d tasks)"):format(#rows))
  else
    print(("(%d shown, %d done)"):format(#rows, c:one("select count(*) n from task where state='done'").n))
  end
  for _, x in ipairs(c:all("select name, role, stay from agent where ended is null and stay is not null order by name")) do
    print(("staying: %s%s: %s"):format(x.name, x.role and (" " .. x.role) or "", x.stay))
  end
end

-- Repo rules every spawn's first message carries (set by the communicator).
function M.cmd_rules(c, a)
  if a.act == "set" then
    c:exec("insert or replace into meta(k,v) values('rules',?)", table.concat(a.text, " "))
  end
  local r = c:one("select v from meta where k='rules'")
  print(r and (r.v or "None") or "(none)")
end

-- Intent before effect (sw-ownership §4.3): the name and task #tid become the new agent's in one transaction.
-- A peer that claimed it first raises {exit = 1, lost = msg} (Python's LostRace), which watchd catches.
function M.reserve(c, name, tid, model)
  local t = util.now()
  return c:tx(function()
    agents.reserve(c, name, model)  -- a failed check below rolls it back
    local r = c:one("select * from task where id=?", tid)
    if not r then util.die("no task #" .. d(tid)) end
    local u = M.undone(c, r)
    if #u > 0 then util.die(("#%s waits on %s"):format(d(tid), ids(u, function(x) return "#" .. d(x.id) end))) end
    if r.state ~= "open" then
      error({ exit = 1, lost = ("task #%s is %s%s"):format(d(tid), r.state, owned(r)) }, 0)
    end
    c:exec("update task set state='claimed', owner=?, lease_until=?, first_claimed_at=coalesce(first_claimed_at,?) where id=?",
      name, t + M.LEASE, t, tid)
    db.log(c, name, "claim", nil, ("#%s %s"):format(d(tid), r.title))
    return r
  end)
end

-- Launch failed: end the row and reopen the task (r, when spawn reserved one), if the new agent still holds it.
function M.unreserve(c, name, r)
  c:tx(function()
    c:exec("update agent set ended=? where name=? and hc is null", util.now(), name)
    if not r then return end
    c:exec("update task set state='open', owner=null, lease_until=null, first_claimed_at=? where id=? and owner=? "
      .. "and state='claimed'", r.first_claimed_at, r.id, name)
  end)
end

return M
