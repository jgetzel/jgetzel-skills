-- Replays runs of the Lean model in swarm/model (SwarmModel/Model.lean, instance `replay`) through the real CLI
-- against a scratch swarm.db: each model action becomes the command (or, for time and the environment, the db
-- write) it stands for, and after every step the db must match the model's state. One test per trace file.
-- Traces (.json, or gzipped, written by SwarmModel/Traces.lean): $SWARM_MODEL_TRACES, else the committed
-- swarm/model/traces/ (swarm/model/replay.sh makes fresh ones).
local json, util = require "swarm.json", require "swarm.util"
local lfs = require "lfs"
local unistd = require "posix.unistd"
local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
local DIR = os.getenv("SWARM_MODEL_TRACES") or (here .. "/../../model/traces")
local COMMS, ROSTER, CAP = "m-comms", 2, "2"
local SYS = { released = "system", digest = "system", dm = "dm", answer = "dm" }

-- the model's unread ids for a (Model.lean's unread)
local function model_unread(st, a)
  local r = {}
  for i = st.cursor[a] + 1, #st.log do
    local m = st.log[i]
    if (m.to == a or m.to == "@all") and m.frm ~= a then r[#r + 1] = i end
  end
  return r
end

-- The model's agents are slots: a spawn fills the first one not live, so an ended slot comes back as a new
-- agent. N maps each slot to the real name of its current agent.
-- M maps slots for this step's new messages: N from before the step, since a tick posts before it spawns.
local function check(t, st, where, N, seen, M)
  M = M or N
  local function fail(what, got, want)
    error(("%s: %s: db has %s, model has %s"):format(where, what, t.repr and t.repr(got) or tostring(got), tostring(want)), 0)
  end
  local now = util.now()
  for id, m in pairs(st.task) do
    local r = t:q1("select * from task where id=?", id)
    if m.st == "absent" then
      if r then fail("task #" .. id, r.state, "absent") end
    else
      if not r or r.state ~= m.st then fail("task #" .. id .. " state", r and r.state, m.st) end
      if (m.st == "claimed" or m.st == "blocked") and r.owner ~= N[m.owner] then
        fail("task #" .. id .. " owner", r.owner, N[m.owner])
      end
      if (m.st == "open" or m.st == "dropped") and r.owner then fail("task #" .. id .. " owner", r.owner, "none") end
      if m.st == "claimed" and ((r.lease_until or 0) > now) ~= m.lease then fail("task #" .. id .. " lease live", r.lease_until, m.lease) end
      if m.st == "done" and ((r.evidence or "") ~= "") ~= m.ev then fail("task #" .. id .. " evidence", r.evidence, m.ev) end
      if (r.answer ~= nil) ~= m.answer then fail("task #" .. id .. " answer", r.answer, m.answer) end
    end
  end
  for slot, g in pairs(st.ag) do
    local name = N[slot]
    local r = name and t:q1("select * from agent where name=?", name)
    if g.st == "unborn" then
      if name then fail("agent " .. slot, name, "unborn") end
    elseif g.st == "ended" then
      if not r or not r.ended then fail("agent " .. name .. " ended", r and r.ended, "ended") end
    elseif not r or r.ended or r.status ~= g.st then
      fail("agent " .. name .. " status", r and (r.ended and "ended" or r.status), g.st)
    end
  end
  local held = 0
  for p, l in pairs(st.lock) do
    local r = t:q1("select agent from lock where path=?", p)
    if (r and r.agent or "") ~= (N[l.holder] or "") then fail("lock " .. p, r and r.agent, N[l.holder]) end
    if l.holder ~= "" then held = held + 1 end
  end
  local n = t:q1("select count(*) n from lock").n
  if n ~= held then fail("lock rows", n, held) end
  -- messages to agents (the communicator's are outside the model), in order; real id -> model id
  local rows, idx = t:q("select * from msg where dest!=? order by id", COMMS), {}
  if #rows ~= #st.log then fail("messages", #rows, #st.log) end
  for i, r in ipairs(rows) do
    local m = st.log[i]
    if i > seen.n and (r.dest ~= M[m.to] or r.kind ~= SYS[m.kind] or (r.urgent ~= 0) ~= m.urgent) then
      fail("message " .. i, r.dest .. " " .. r.kind, tostring(M[m.to]) .. " " .. m.kind)
    end
    idx[r.id] = i
  end
  seen.n = #rows
  for slot, g in pairs(st.ag) do
    local name = N[slot]
    if g.st ~= "unborn" and g.st ~= "ended" then
      local cur = t:q1("select last_msg_id from cursor where agent=?", name)
      local got = {}
      for _, r in ipairs(t:q("select id from msg where id>? and frm!=? and (dest=? or dest='@all') order by id",
          cur and cur.last_msg_id or 0, name, name)) do
        got[#got + 1] = idx[r.id]
      end
      local want = model_unread(st, slot)
      if table.concat(got, ",") ~= table.concat(want, ",") then
        fail("unread of " .. slot, table.concat(got, ","), table.concat(want, ","))
      end
    end
  end
end

local function setdb(t, sql, ...) t:q(sql, ...) end

-- one model action, done to the db the way the code (or the world) does it
local function act(t, name, p, N)
  local now = util.now()
  local function hc(who)  -- a spawned agent is bound to the terminal the launch made: its commands come from there
    local r = t:q1("select hc from agent where name=?", who)
    return r and r.hc or nil
  end
  for k, x in pairs(p) do
    if k:match("^[ab]%d+$") then p[k] = N[x] or error("slot " .. x .. " has no agent", 0) end
  end
  local function sw(who, ...)
    local args = { ... }
    local o = type(args[#args]) == "table" and table.remove(args) or {}
    o.hc = hc(who)
    args[#args + 1] = o
    return t:sw(who, unpack(args))
  end
  local function hook(who, ev) return t:hook(who, ev, {}, hc(who)) end
  local function ids(set) local s = {} for i, x in ipairs(set) do s[i] = tostring(x) end return table.concat(s, ",") end
  if name == "claim" then sw(p.a1, "task", "claim", tostring(p.t1))
  elseif name == "renew" then sw(p.a4, "task", "renew", tostring(p.t4))
  elseif name == "release" then sw(p.a5, "task", "release", tostring(p.t5))
  elseif name == "block" then sw(p.a6, "task", "block", tostring(p.t6), "which way?")
  elseif name == "done" then sw(p.a7, "task", "done", tostring(p.t7), "--evidence", p.ev7 and "abc1234" or "")
  elseif name == "dropOwn" then sw(p.a8, "task", "drop", tostring(p.t8))
  elseif name == "lock" then sw(p.a9, "lock", p.p9)
  elseif name == "unlock" then sw(p.a10, "unlock", p.p10)
  elseif name == "postTo" then
    if p.u11 then sw(p.a11, "post", "--urgent", p.b11, "hi") else sw(p.a11, "post", p.b11, "hi") end
  elseif name == "readAll" then sw(p.a12, "read")
  elseif name == "stop" then
    hook(p.a14, "stop")  -- the Stop hook's waiter: this process stands in for it, alive until waiterGone or a wake
    setdb(t, "update agent set ctx_tokens=?, waiter=? where name=?", p.big14 and 100000 or 1000, unistd.getpid(), p.a14)
  elseif name == "wake" then
    local r = sw(p.a15, "wait", "--timeout", "5", "--poll", "0.1", { ok = false })
    if r.code ~= 2 then error(("swarm wait exited %d, the model woke it: %s"):format(r.code, r.stderr), 0) end
    hook(p.a15, "prompt")
  elseif name == "prompt" then hook(p.a18, "prompt")
  elseif name == "boot" then hook(p.a19, "prompt")
  elseif name == "waiterGone" then setdb(t, "update agent set waiter=null where name=?", p.a20)
  elseif name == "age" then setdb(t, "update agent set last_active=? where name=?", now - 200, p.a21)
  elseif name == "cool" then setdb(t, "update agent set last_active=? where name=?", now - 4000, p.a22)
  elseif name == "expire" then setdb(t, "update task set lease_until=? where id=?", now - 10, p.t23)
  elseif name == "expireLock" then setdb(t, "update lock set lease_until=? where path=?", now - 10, p.p24)
  elseif name == "leave" then sw(p.a25, "leave")
  elseif name == "add" then
    if #p.d28 > 0 then sw(COMMS, "task", "add", "a task", "--after", ids(p.d28)) else sw(COMMS, "task", "add", "a task") end
  elseif name == "after" then
    if #p.d29 > 0 then sw(COMMS, "task", "after", tostring(p.t29), ids(p.d29))
    else sw(COMMS, "task", "after", tostring(p.t29)) end
  elseif name == "unblock" then sw(COMMS, "task", "unblock", tostring(p.t30), "--answer", "go left")
  elseif name == "drop" then sw(COMMS, "task", "drop", tostring(p.t31))
  elseif name == "tick" then sw(COMMS, "watchd", "--once", "--comms", COMMS, "--max-agents", CAP, "--min-free-mem", "0")
  else error("no replay for model action " .. name, 0) end
end

local function replay(t, file)
  local text = file:match("%.gz$") and t:exec({ "gzip", "-dc", file }).stdout or util.slurp(file)
  local trace = json.decode(text)
  t:fakes()
  local s0 = trace.states[1].s
  local roster = {}
  for name, g in pairs(s0.ag) do if g.st == "working" then roster[#roster + 1] = name end end
  table.sort(roster)
  if #roster ~= ROSTER then error("trace roster is not " .. ROSTER, 0) end
  for _, name in ipairs(roster) do
    t:agent(name)
    t:hook(name, "prompt", {})
  end
  t:q("insert or replace into meta(k,v) values('comms',?)", COMMS)  -- as `swarm start` records it
  local N, seen, prev = {}, { n = 0 }, s0
  for _, name in ipairs(roster) do N[name] = name end
  check(t, s0, "init", N, seen)
  for i = 2, #trace.states do
    local x = trace.states[i]
    local name, picks = x.action, x.picks
    local where = ("step %d %s %s"):format(i - 1, name, t.repr(picks))
    local ok, err = pcall(act, t, name, picks, N)
    if not ok then error(where .. ": " .. tostring(err), 0) end
    local st = x.s
    local M = {}
    for k, n in pairs(N) do M[k] = n end
    -- a spawn: the slot's agent is whoever the db gave its task to. The same tick may end a booting slot's agent
    -- and fill the slot again, so a booting slot is remapped whenever the db's owner differs, if the old one ended.
    for slot, g in pairs(st.ag) do
      if g.boot then
        for id, k in pairs(st.task) do
          if k.owner == slot and k.st == "claimed" then
            local r = t:q1("select owner, state from task where id=?", id)
            if not (r and r.owner) then
              error(("%s: the model spawned %s for task #%d; the db's is %s with no owner"):format(where, slot, id, r and r.state), 0)
            end
            if r.owner ~= N[slot] then
              local old = N[slot] and prev.ag[slot].boot and t:q1("select status from agent where name=?", N[slot])
              if old and old.status ~= "ended" then
                error(("%s: task #%d went to %s while %s (slot %s) is %s"):format(where, id, r.owner, N[slot], slot, old.status), 0)
              end
              N[slot] = r.owner
            end
          end
        end
      end
    end
    check(t, st, where, N, seen, M)
    prev = st
  end
end

local T = {}
if lfs.attributes(DIR, "mode") == "directory" then
  for f in lfs.dir(DIR) do
    if f:match("%.json$") or f:match("%.json%.gz$") then
      T["trace " .. f] = function(t)
        t.repr = require("test.cli").repr
        replay(t, DIR .. "/" .. f)
      end
    end
  end
end
return T
