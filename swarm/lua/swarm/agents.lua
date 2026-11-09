-- Agent rows: the fence, binding, the cold-cache rule, release; cmd join/leave/who.
local util, proc, json, db = require "swarm.util", require "swarm.proc", require "swarm.json", require "swarm.db"
local unistd = require "posix.unistd"
local M = {}

M.COLD_IDLE = 55 * 60   -- prompt cache (1 h TTL) counts as warm for this long
M.SMALL_CTX = 40000     -- a wake of a context this small is cheap whatever the cache

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

-- Bind name to terminal hc (join, spawn): a new, ended or unbound row, or one whose terminal isn't live.
-- A live binding elsewhere moves only with takeover, logged old -> new.
function M.bind(c, name, cwd, hc, model, takeover)
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

function M.is_comms(c, name)
  if not name or name == "" then return false end
  local cm = c:one("select v from meta where k='comms'")
  return util.endswith(name, "comms") or name == (cm and cm.v or M.env("SWARM_COMMS"))
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
  c:exec("update task set state='open', owner=null, lease_until=null, question=null where owner=? and state in ('claimed','blocked')", name)
  c:exec("delete from lock where agent=?", name)
  c:exec("delete from conflict where a=? or b=?", name, name)
  c:exec("delete from pairkey where a=? or b=?", name, name)
end

function M.release(c, name)
  c:tx(function() M._release(c, name) end)
end

-- ---------- commands ----------

function M.cmd_join(c, a)
  local n = a.name or M.me()
  M.bind(c, n, unistd.getcwd(), M.env("HC_TERMINAL_ID"), a.model, a.takeover)
  db.log(c, n, "join")
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
  local out = require("swarm.proc").run({ "sh", "-c", "cat install.lua calendar/* ../swarm/herdr/mods/swarm/swarm.svg | sha256sum" },
    here .. "/../herdr-mods")
  if out and util.strip(out):sub(1, 64) ~= have then return "herdr panel: out of date: run install.sh" end
end

function M.cmd_who(c, a)
  local machine, conflict = require "swarm.machine", require "swarm.conflict"
  local t = util.now()
  local wts = conflict.wt_map(c)
  local avail, total, psi = machine.mem_psi()
  if avail then print(machine.machine_line(avail, total, psi)) end
  local stale = M.herdr_stale()
  if stale then print(stale) end
  for _, x in ipairs(M.live_agents(c)) do
    local k = math.floor((x.ctx_tokens or 0) / 1000)
    local last = M.session_active(x, t)
    local cache = t - last < M.COLD_IDLE and "warm" or "cold"
    local sn = x.snap and util.startswith(x.snap, "{") and json.decode(x.snap) or {}
    local fs = type(sn) == "table" and type(sn.files) == "table" and sn.files or {}
    local lk = {}
    for _, r in ipairs(c:all("select path from lock where agent=?", x.name)) do lk[#lk + 1] = r.path end
    local s = ("%s %s ctx=%dk idle=%s cache=%s"):format(x.name, x.status, k, util.ago(last), cache)
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
