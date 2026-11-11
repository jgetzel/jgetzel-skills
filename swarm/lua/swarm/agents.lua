-- Agent rows: the fence, binding, the cold-cache rule, release; cmd join/leave/who.
local util, proc, json, db = require "swarm.util", require "swarm.proc", require "swarm.json", require "swarm.db"
local unistd = require "posix.unistd"
local M = {}

M.COLD_IDLE = 55 * 60   -- prompt cache (1 h TTL) counts as warm for this long
M.SMALL_CTX = 40000     -- a wake of a context this small is cheap whatever the cache
M.HUMAN = "human"       -- the user's name (the panel runs the CLI as it): the communicator's rights, never an agent row

function M.env(k)  -- an env var, nil when unset or empty (Python's `os.environ.get(k)` truthiness)
  local v = os.getenv(k)
  if v == "" then return nil end
  return v
end

function M.me()
  return M.env("SWARM_NAME") or util.die("SWARM_NAME is unset (run as a swarm agent, or export SWARM_NAME)")
end

-- Why this terminal may not write as name (sw-ownership §4.2, §4.4), or nil: the bound terminal is the token.
function M.fence(c, name)
  local r = c:one("select hc, ended from agent where name=?", name)
  if not r then return nil end
  if r.ended then
    local why = c:one("select data from event where agent=? and kind in ('reap','leave','end') order by id desc limit 1", name)
    local tail = why and why.data and why.data ~= "" and (" (" .. why.data .. ")") or ""
    return ("%s was ended at %s%s; `swarm join` to return."):format(name, util.hhmm(r.ended), tail)
  end
  local here = M.env("HC_TERMINAL_ID")
  if r.hc and r.hc ~= "" and r.hc ~= here then
    return ("%s is bound to %s; this terminal is %s. `swarm join --takeover` moves it here."):format(
      name, r.hc, here or "outside Herdr")
  end
  return nil
end

function M.hc_terminals()
  local out = proc.run({ "hc", "ls", "--json" })
  local j = out and json.decode(out)
  return type(j) == "table" and type(j.terminals) == "table" and j.terminals or nil
end

-- The labels hc keeps on terminal addr: its Herdr space and, for a communicator, the db it is the communicator of.
function M.hc_info(addr)
  local out = addr and proc.run({ "hc", "get", addr })
  local j = out and json.decode(out)
  local l = type(j) == "table" and type(j.labels) == "table" and j.labels or {}
  return { space = l["herdr.space"], comms = l["swarm.comms"] }
end

function M.label_comms(addr)
  proc.run({ "hc", "label", addr, "swarm.comms=" .. db.dbpath() })
end

-- Bind name to terminal hc (join, spawn): a new, ended or unbound row, or one whose terminal isn't live.
-- A live binding elsewhere moves only with takeover, logged old -> new.
function M.bind(c, name, cwd, hc, model, takeover)
  M.not_human(name)
  local r = c:one("select hc, ended from agent where name=?", name)
  local old = r and not r.ended and r.hc ~= "" and r.hc or nil
  local here = hc or "outside Herdr"
  if old and old ~= hc and not takeover then
    local terms, live = M.hc_terminals(), false  -- outside any transaction; nil (no hc) can't show it dead
    if terms == nil then live = true end
    for _, x in ipairs(terms or {}) do
      if x.state == "live" and x.address == old then live = true end
    end
    if live then
      util.die(("%s is bound to %s; this terminal is %s. `swarm join --takeover` moves it here."):format(name, old, here))
    end
  end
  c:tx(function()
    local r2 = c:one("select hc, ended from agent where name=?", name)
    if (r == nil) ~= (r2 == nil) or (r and (r.hc ~= r2.hc or r.ended ~= r2.ended)) then
      util.die(name .. "'s binding changed under you; run it again")
    end
    local t = util.now()
    c:exec("insert or ignore into agent(name,cwd,status,last_active,started) values(?,?,?,?,?)", name, cwd, "idle", t, t)
    if r == nil then M.new_inbox(c, name) end
    c:exec("update agent set hc=?, ended=null, model=coalesce(?,model), "
      .. "status=case when ended is null then status else 'idle' end where name=?", hc, model, name)
    if old and old ~= hc then
      db.log(c, name, "takeover", nil, old .. " -> " .. here)
    end
  end)
end

-- A new agent's inbox starts now: earlier broadcasts (often an older run's) aren't for it. Call it wherever an
-- agent row is created; a row that already has a cursor keeps it.
function M.new_inbox(c, name)
  c:exec("insert or ignore into cursor(agent,last_msg_id) select ?, coalesce(max(id),0) from msg", name)
end

-- Write name's own fields, fenced: nothing for an ended row or another terminal's (returns why).
-- A new row is bound here; bind=true (wait) also binds an unbound one. Only join moves a binding.
function M.touch(c, name, cwd, bind, kw)
  if name == M.HUMAN then return nil end
  local why = M.fence(c, name)
  if why then return why end
  local here, t = M.env("HC_TERMINAL_ID"), util.now()
  if c:exec("insert or ignore into agent(name,cwd,status,last_active,started,hc) values(?,?,?,?,?,?)", name, cwd, "idle", t, t, here) > 0 then
    M.new_inbox(c, name)
  end
  if bind and here then c:exec("update agent set hc=? where name=? and hc is null", here, name) end
  for k, v in pairs(kw or {}) do  -- keys come from code, never input
    c:exec("update agent set " .. k .. "=? where name=? and ended is null and (hc is null or hc is ?)", v, name, here)
  end
  return nil
end

function M.set_status(c, name, status, kw)
  local old = c:one("select status from agent where name=?", name)
  kw = kw or {}
  kw.last_active, kw.status = util.now(), status
  if M.touch(c, name, nil, false, kw) then return end
  if not old or old.status ~= status then db.log(c, name, "status", nil, status) end
end

function M.live_agents(c)
  return c:all("select * from agent where ended is null order by name")
end

-- Live rows split by the terminal at read time (hc ls), so it holds with no watchd to reap: present, gone.
-- No hc, or an unbound row, can't show a terminal gone.
function M.split_agents(c)
  local terms, live = M.hc_terminals(), {}
  for _, x in ipairs(terms or {}) do
    if x.state == "live" and x.address then live[x.address] = true end
  end
  local here, gone = {}, {}
  for _, x in ipairs(M.live_agents(c)) do
    table.insert(terms ~= nil and x.hc and x.hc ~= "" and not live[x.hc] and gone or here, x)
  end
  return here, gone
end

-- The user's staffing numbers (sw-roles §6): live agents but the communicator, meta agent_min (watchd auto-spawns
-- to it) and agent_max (every spawn refuses at it); nil when unset.
function M.limits(c)
  local function n(k) local r = c:one("select v from meta where k=?", k); return r and tonumber(r.v) end
  local live = 0
  for _, x in ipairs(M.live_agents(c)) do
    if not M.is_comms(c, x.name) then live = live + 1 end
  end
  return live, n("agent_min"), n("agent_max")
end

function M.limits_line(c)
  local live, mn, mx = M.limits(c)
  return ("agents: %d live, %s, %s"):format(live, mn and "auto-spawn to " .. mn or "no auto-spawn number",
    mx and "max " .. mx or "no max set")
end

-- Intent before effect (sw-ownership rule 3): the max check and the new agent's row in one transaction, before
-- the launch, so two spawns can't both take the last place. At the max raises {exit = 1, refused = msg}.
function M.reserve(c, name, model)
  M.not_human(name)
  c:tx(function()
    if c:one("select 1 from agent where name=? and ended is null", name) then util.die(name .. " is a live agent") end
    local live, _, mx = M.limits(c)
    if mx and live >= mx then
      error({ exit = 1, refused = ("%d agents are live and the user's max is %d. The communicator can raise it "
        .. "(`swarm limits --max N`)."):format(live, mx) }, 0)
    end
    local t = util.now()
    c:exec("insert or ignore into agent(name,cwd,status,last_active,started) values(?,?,?,?,?)",
      name, unistd.getcwd(), "idle", t, t)
    M.new_inbox(c, name)
    c:exec("update agent set hc=null, ended=null, status='idle', model=coalesce(?,model) where name=?", model, name)
  end)
end

-- swarm limits [--min N] [--max M]: set the staffing numbers (the communicator, on the user's word); print them.
function M.cmd_limits(c, a)
  if a.min or a.max then
    c:tx(function()
      local _, mn, mx = M.limits(c)
      mn, mx = a.min or mn, a.max or mx
      if mn and mx and mn > mx then util.die(("the auto-spawn number %d is above the max %d"):format(mn, mx)) end
      if a.min then c:exec("insert or replace into meta(k,v) values('agent_min',?)", tostring(a.min)) end
      if a.max then c:exec("insert or replace into meta(k,v) values('agent_max',?)", tostring(a.max)) end
      db.log(c, M.env("SWARM_NAME") or M.HUMAN, "limits", nil, ("min %s max %s"):format(tostring(mn), tostring(mx)))
    end)
  end
  print(M.limits_line(c))
end

-- The user's away flag (meta away = "<since> <note>"): {since, note}, or nil when they are here.
function M.away(c)
  local r = c:one("select v from meta where k='away'")
  return r and { since = tonumber(r.v:match("^%d+")), note = r.v:match("^%d+ (.+)$") } or nil
end

-- What the communicator is told while the user is away (on `swarm away`, and on its read/wait/board).
function M.away_line(aw)
  return ("the user is away since %s%s: don't ask them; decide what is yours to decide, queue the rest."):format(
    util.hhmm(aw.since), aw.note and (" (" .. aw.note .. ")") or "")
end

function M.comms_name(c)
  local cm = c:one("select v from meta where k='comms'")
  return cm and cm.v ~= "" and cm.v or M.env("SWARM_COMMS")
end

-- What happened since `since`, for `swarm away --back` (and state --json's `back`, until the next away).
function M.digest(c, since, note)
  local A, t = json.array, util.now()
  local qs = A()
  for _, r in ipairs(c:all("select id,title,owner,question from task where state='blocked'")) do
    local e = c:one("select max(ts) as ts from event where (kind='block' and (data=? or data like ?)) "
      .. "or (kind='task-blocked' and path=?)", "#" .. util.d(r.id), "#" .. util.d(r.id) .. " %", util.d(r.id))
    r.since = e and e.ts or since
    qs[#qs + 1] = r
  end
  table.sort(qs, function(x, y) return x.since < y.since or (x.since == y.since and x.id < y.id) end)
  local ended = A()
  for _, r in ipairs(c:all("select name, ended from agent where ended>=? order by ended", since)) do
    local why = c:one("select data from event where agent=? and kind in ('reap','leave','end') and ts>=? order by id desc limit 1",
      r.name, since)
    ended[#ended + 1] = { name = r.name, at = r.ended, why = why and why.data or json.null }
  end
  local hung = A()
  for _, r in ipairs(c:all("select distinct e.agent as name from event e join agent g on g.name=e.agent "
      .. "where e.kind='stay-hung' and e.ts>=? and g.ended is null order by e.agent", since)) do
    hung[#hung + 1] = r.name
  end
  local ci = c:one("select sha,status,conclusion,url from ci order by created desc limit 1")
  return { since = since, back = t, note = note or json.null, questions = qs,
    done = A(c:all("select id,title,owner,evidence,done_at from task where state='done' and done_at>=? order by done_at", since)),
    merged = A(c:all("select id,title,pr,merged_at from task where merged_at>=? order by merged_at", since)),
    ci = ci or json.null, ended = ended, hung = hung }
end

function M.digest_text(g)
  local L = { ("back: away since %s%s, %s"):format(util.hhmm(g.since), type(g.note) == "string" and (" (" .. g.note .. ")") or "",
    util.ago(g.since)) }
  L[#L + 1] = #g.questions == 0 and "no questions wait" or ("%d question%s wait, oldest first:"):format(
    #g.questions, #g.questions == 1 and "" or "s")
  for _, q in ipairs(g.questions) do
    L[#L + 1] = ("  #%s %s (%s): %s  [%s]"):format(util.d(q.id), q.owner or "-", util.hhmm(q.since), q.question or "?", q.title)
  end
  local function list(head, rows, f)
    if #rows == 0 then return end
    local p = {}
    for i, r in ipairs(rows) do p[i] = f(r) end
    L[#L + 1] = head .. table.concat(p, ", ")
  end
  list("finished: ", g.done, function(r) return ("#%s %s"):format(util.d(r.id), r.title) end)
  list("merged: ", g.merged, function(r) return ("PR #%s (#%s)"):format(r.pr and util.d(r.pr) or "?", util.d(r.id)) end)
  local ci = type(g.ci) == "table" and g.ci or nil
  L[#L + 1] = "main CI: " .. (ci and ("%s %s"):format(ci.conclusion or ci.status or "?", (ci.sha or ""):sub(1, 7)) or "no run seen")
  list("ended: ", g.ended, function(r) return r.name .. (type(r.why) == "string" and (" (" .. r.why .. ")") or "") end)
  list("hung: ", g.hung, function(r) return r end)
  return table.concat(L, "\n")
end

-- swarm away [note] | --back: the user's away flag. Away: the communicator is told once; questions queue (watchd and
-- `task block`). Back: one urgent message to the communicator and the digest, kept in meta away_digest until the next away.
function M.cmd_away(c, a)
  local me, comms = M.env("SWARM_NAME") or M.HUMAN, M.comms_name(c)
  local msgs = require "swarm.msgs"
  if a.back then
    local g = c:tx(function()
      local aw = M.away(c)
      if not aw then return nil end
      local g = M.digest(c, aw.since, aw.note)
      c:exec("delete from meta where k='away'")
      c:exec("insert or replace into meta(k,v) values('away_digest',?)", json.encode(g))
      db.log(c, me, "back")
      if comms then
        local ids = {}
        for i, q in ipairs(g.questions) do ids[i] = "#" .. util.d(q.id) end
        msgs.post(c, me, comms, ("the user is back: %d question%s wait%s"):format(#ids, #ids == 1 and "" or "s",
          #ids > 0 and " (" .. table.concat(ids, ", ") .. ")" or ""), true, "system")
      end
      return g
    end)
    print(g and M.digest_text(g) or "you were not away")
    return
  end
  local note = util.strip(table.concat(a.note, " "))
  local was = c:tx(function()
    local aw = M.away(c)
    if aw then return aw end
    c:exec("delete from meta where k='away_digest'")
    c:exec("insert or replace into meta(k,v) values('away',?)", util.strip(util.now() .. " " .. note))
    db.log(c, me, "away", nil, note)
    if comms then msgs.post(c, me, comms, M.away_line(M.away(c)), false, "system") end
  end)
  if was then print(("already away since %s"):format(util.hhmm(was.since))) return end
  print("away" .. (note ~= "" and ": " .. note or "") .. "; questions wait for you, work goes on")
end

function M.is_comms(c, name)
  if not name or name == "" then return false end
  local cm = c:one("select v from meta where k='comms'")
  return name == (cm and cm.v or M.env("SWARM_COMMS"))
end

-- The communicator's rights (end, release or drop another's task, unblock): it, or the user.
function M.in_charge(c, name)
  return name == M.HUMAN or M.is_comms(c, name)
end

function M.not_human(name)
  if name == M.HUMAN then util.die("'human' is the user's name (the panel acts as it); an agent can't take it") end
end

-- ---------- cold-cache rule ----------

local term_seen = {}  -- hc address -> {fetched_at, session's last status change in epoch s}

-- Later of last_active and the hc session's last status change: an agent that doesn't run
-- the swarm hooks (the comms) still has a warm cache while its session is taking turns.
function M.session_active(a, t)
  local last = a.last_active or 0
  if not a.hc or a.hc == "" or t - last < M.COLD_IDLE then return last end
  local seen = term_seen[a.hc]
  if not seen or t - seen[1] > 30 then
    local j = json.decode(proc.run({ "hc", "get", a.hc, "--json" }) or "{}")
    local ms = type(j) == "table" and tonumber(j.status_ms) or 0
    seen = { t, math.floor(ms / 1000) }
    term_seen[a.hc] = seen
  end
  return math.max(last, seen[2])
end

-- nil if waking agent row a is cheap, else why it is a cold wake.
function M.cold_reason(a, t)
  t = t or util.now()
  if a.status == "working" or (a.ctx_tokens or 0) < M.SMALL_CTX then return nil end
  local last = M.session_active(a, t)
  if (a.compacted_at or 0) >= last or t - last < M.COLD_IDLE then return nil end
  local k = math.floor(a.ctx_tokens / 1000)
  return ("%s is idle %d min with ~%dk context and no compaction; a wake costs ~%dk uncached tokens."):format(
    a.name, math.floor((t - last) / 60), k, k)
end

-- ---------- release ----------

function M._release(c, name)
  c:exec("update agent set stay=null where name=?", name)  -- a held thing, like a claim: an ended agent holds none
  c:exec("update task set state='open', owner=null, lease_until=null, question=null where owner=? and state in ('claimed','blocked')", name)
  c:exec("delete from lock where agent=?", name)
  c:exec("delete from conflict where a=? or b=?", name, name)
  c:exec("delete from pairkey where a=? or b=?", name, name)
end

function M.release(c, name)
  c:tx(function() M._release(c, name) end)
end

-- One line of at most 80 characters: a field peers read (and peers are data).
function M.one_line(s)
  return util.cut(util.strip((s:gsub("%s+", " "))), 80)
end

-- Set name's role (a label nothing decides by) and log it; returns the live peers declaring the same text.
function M.set_role(c, name, text)
  text = M.one_line(text)
  c:exec("update agent set role=? where name=?", text ~= "" and text or nil, name)
  db.log(c, name, "role", nil, text)
  local same = {}
  if text == "" then return same end
  for _, r in ipairs(c:all("select name from agent where ended is null and name!=? and lower(role)=lower(?) order by name",
    name, text)) do
    same[#same + 1] = ("%s also declares '%s'"):format(r.name, text)
  end
  return same
end

-- ---------- commands ----------

function M.cmd_role(c, a)
  local n = M.me()
  if #a.text == 0 then
    local r = c:one("select role from agent where name=?", n)
    print(r and r.role or "(none)")
    return
  end
  local same = c:tx(function()
    local why = M.touch(c, n, unistd.getcwd(), false)
    if why then util.die(why) end
    return M.set_role(c, n, table.concat(a.text, " "))
  end)
  for _, s in ipairs(same) do print(s) end
end

-- The communicator's terminal is in the swarm's space (meta.space, set by the first communicator) and is no other
-- swarm's communicator, takeover or not for the space, only by takeover for the other swarm.
function M.cmd_join(c, a)
  local n = a.name or M.me()
  local here = M.env("HC_TERMINAL_ID")
  local comms = here and M.is_comms(c, n)
  if comms then
    local i, sp = M.hc_info(here), c:one("select v from meta where k='space'")
    if sp and i.space and i.space ~= sp.v then
      util.die(("%s is the communicator of a swarm in space %s; this terminal is in space %s."):format(n, sp.v, i.space))
    end
    if i.comms and i.comms ~= db.dbpath() and not a.takeover then
      util.die(("this terminal is the communicator of another swarm (%s). `swarm join --takeover` takes it for this one."):format(i.comms))
    end
  end
  M.bind(c, n, unistd.getcwd(), here, a.model, a.takeover)
  if comms then
    M.label_comms(here)
    local sp = M.hc_info(here).space
    if sp then c:exec("insert or ignore into meta(k,v) values('space',?)", sp) end
  end
  db.log(c, n, "join")
end

function M.stay_of(c, name)
  local r = name and c:one("select stay from agent where name=?", name)
  return r and r.stay
end

function M.cmd_stay(c, a)
  local n = M.me()
  if #a.text == 0 and not a["end"] then
    local s = M.stay_of(c, n)
    print(s and ("you stay for '%s'"):format(s) or "you stay for nothing: watchd ends you once idle, holding nothing, work landed")
    return
  end
  local v = not a["end"] and M.one_line(table.concat(a.text, " ")) or nil
  if v == "" then util.die("say what you wait for: swarm stay \"<what>\"") end
  c:tx(function()
    local why = M.touch(c, n, nil, false)
    if why then util.die(why) end
    c:exec("update agent set stay=? where name=?", v, n)
    db.log(c, n, v and "stay" or "stay-end", nil, v)
  end)
  print(v and ("you stay for '%s'; watchd won't end you. `swarm stay --end` when it is over."):format(v)
    or "stay ended: watchd ends you once you are idle, hold nothing and your work is on your task's base.")
end

function M.cmd_leave(c, a)
  local n = a.name or M.me()
  c:tx(function()
    c:exec("update agent set ended=?, status='ended' where name=?", util.now(), n)
    M._release(c, n)
    db.log(c, n, "leave")
  end)
end

-- Notice when install.sh's Herdr copies (jgetzel-tabs, layouts/jgetzel.json, or an older install's swarm-tabs)
-- predate this checkout's herdr-mods/install.lua.
function M.herdr_stale()
  local home = os.getenv("HERDR_APP_HOME") or ((os.getenv("HOME") or "") .. "/.config/herdr-app")
  local here, lfs = os.getenv("SWARM_HERE"), require "lfs"
  if not here or not (lfs.attributes(home .. "/mods/jgetzel-tabs", "mode") or lfs.attributes(home .. "/mods/swarm-tabs", "mode")) then
    return nil
  end
  local f = io.open(home .. "/jgetzel-install.stamp")
  local have = f and util.strip(f:read("*a")) or ""
  if f then f:close() end
  local out = require("swarm.proc").run({ "sh", "-c", "cat install.lua calendar/* ../swarm/herdr/mods/swarm/swarm.svg | { sha256sum 2>/dev/null || shasum -a 256; }" },
    here .. "/../herdr-mods")
  if out and util.strip(out):sub(1, 64) ~= have then return "herdr panel: out of date: run install.sh" end
end

function M.cmd_who(c, a)
  local machine, conflict = require "swarm.machine", require "swarm.conflict"
  local t = util.now()
  local wts = conflict.wt_map(c)
  print(M.limits_line(c))
  local avail, total, psi = machine.mem()
  if avail then print(machine.machine_line(avail, total, psi)) end
  local stale = M.herdr_stale()
  if stale then print(stale) end
  local here, gone = M.split_agents(c)
  for _, x in ipairs(gone) do
    print(("%s gone: no terminal; swarm join --takeover %s"):format(x.name, x.name))
  end
  for _, x in ipairs(here) do
    local k = math.floor((x.ctx_tokens or 0) / 1000)
    local last = M.session_active(x, t)
    local cache = t - last < M.COLD_IDLE and "warm" or "cold"
    local sn = x.snap and util.startswith(x.snap, "{") and json.decode(x.snap) or {}
    local fs = type(sn) == "table" and type(sn.files) == "table" and sn.files or {}
    local lk = {}
    for _, r in ipairs(c:all("select path from lock where agent=?", x.name)) do lk[#lk + 1] = r.path end
    local s = ("%s %s%s%s ctx=%dk idle=%s cache=%s"):format(x.name, x.status, x.role and (" role=" .. x.role) or "",
      x.stay and (' stays: "%s"'):format(x.stay) or "", k, util.ago(last), cache)
      .. (M.cold_reason(x, t) and " COLD-GUARDED" or "")
      .. " wt: " .. (wts[x.name] and util.basename(wts[x.name]) or "?")
    if #fs > 0 then
      s = s .. " files: " .. table.concat(fs, ", ", 1, math.min(5, #fs)) .. (#fs > 5 and (" +%d more"):format(#fs - 5) or "")
    end
    if #lk > 0 then s = s .. " locks: " .. table.concat(lk, ", ") end
    print(s)
  end
end

return M
