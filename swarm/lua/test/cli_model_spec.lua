-- Replays runs of the Lean model in swarm/model (SwarmModel/Model.lean, instance `replay`) through the real CLI
-- against a scratch swarm.db: each model action becomes the command (or, for time and the environment, the db
-- write) it stands for, and after every step the db must match the model's state. One test per trace file.
-- Traces (.json, or gzipped, written by SwarmModel/Traces.lean): $SWARM_MODEL_TRACES, else the committed
-- swarm/model/traces/ (swarm/model/replay.sh makes fresh ones).
local json, util = require "swarm.json", require "swarm.util"
local lfs = require "lfs"
local unistd = require "posix.unistd"
local stdlib = require "posix.stdlib"
local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
local DIR = os.getenv("SWARM_MODEL_TRACES") or (here .. "/../../model/traces")
local COMMS, ROSTER, CAP = "m-comms", 2, "2"
local SYS = { released = "system", digest = "system", nudge = "system", dm = "dm", answer = "dm" }

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

-- ---- git: the model's worktree slots, branches and commits in the fixture's repo ----
-- G.P[w] the path of worktree slot w's current incarnation, G.BR[b] branch b's name, G.C[k] model commit k's sha.
-- The main checkout (t.repo) is detached and outside the model; branches 0.. are bases (main, formal, ..).
local function real(p) return p and (stdlib.realpath(p) or p) end
local function out(t, cwd, ...) return util.strip(t:git(cwd, ...)) end

local function git_setup(t, s0)
  local G = { P = {}, BR = { [0] = "main" }, C = {}, k = 0, n = 0, pid = {} }
  G.nbases = #s0.brs - #s0.wts
  t:git(t.repo, "worktree", "remove", "--force", t.wt)
  t:git(t.repo, "branch", "-D", "w2")
  for b = 1, G.nbases - 1 do
    G.BR[b] = b == 1 and "formal" or ("base" .. b)
    t:git(t.repo, "branch", G.BR[b])
    -- bases are data (sw-bases): a dropped task names each one, so the sweep protects it as the model's bases are
    t:q("insert into task(id,title,state,base) values(?,?,'dropped',?)", -b, "base " .. b, G.BR[b])
  end
  t:q("update sqlite_sequence set seq=0 where name='task'")  -- the model's tasks are still #1..
  t:git(t.repo, "checkout", "-q", "--detach")
  G.C[0] = out(t, t.repo, "rev-parse", "HEAD")
  t:defer(function() for _, pid in pairs(G.pid) do os.execute("kill " .. pid .. " 2>/dev/null") end end)
  return G
end

-- the git half of one model action; false if it isn't one
local function gitact(t, name, p, G, hc)
  local function path(w) return G.P[w] or error("worktree " .. w .. " was never added", 0) end
  if name == "gitAdd" then
    G.k = G.k + 1
    G.P[p.w40] = ("%s/wt%d-%s"):format(t.d, G.k, p.a40)
    G.BR[G.nbases + p.w40] = ("%s/w%d-%d"):format(p.a40, p.w40, G.k)
    t:git(t.repo, "worktree", "add", "-q", "-b", G.BR[G.nbases + p.w40], G.P[p.w40], "main")
  elseif name == "gitEdit" then
    G.n = G.n + 1
    local f = ("%s/f%d.txt"):format(path(p.w41), G.n)
    local h = assert(io.open(f, "w")); h:write("f" .. G.n .. "\n"); h:close()
    t:hook(p.a41, "pre-tool", { tool_name = "Edit", tool_input = { file_path = f } }, hc(p.a41))
  elseif name == "gitCommit" then
    t:git(path(p.w42), "add", "-A")
    t:git(path(p.w42), "commit", "-qm", "c")
  elseif name == "gitLand" then t:git(path(p.w43), "push", "-q", ".", "HEAD:" .. G.BR[p.r43])
  elseif name == "gitSquash" then
    local tmp, head = t.d .. "/squash", out(t, path(p.w44), "rev-parse", "HEAD")
    t:git(t.repo, "worktree", "add", "-q", "--detach", tmp, G.BR[p.r44])
    t:git(tmp, "merge", "-q", "--squash", head)
    t:git(tmp, "commit", "-qm", "squash")
    t:git(tmp, "push", "-q", ".", "HEAD:" .. G.BR[p.r44])
    t:git(t.repo, "worktree", "remove", "--force", tmp)
  elseif name == "gitCheckout" then t:git(path(p.w45), "checkout", "-q", G.BR[p.r45])
  elseif name == "wtAge" then  -- what sweep reads: the directory's and the HEAD log's mtime
    local old = util.now() - 3600
    lfs.touch(path(p.w46), old, old)
    lfs.touch(out(t, path(p.w46), "rev-parse", "--absolute-git-dir") .. "/logs/HEAD", old, old)
  elseif name == "wtProc" then
    if p.v47 then
      G.pid[p.w47] = util.strip(t:exec({ "sh", "-c", "cd \"$1\" && { sleep 3600 >/dev/null 2>&1 & echo $!; }", "_", path(p.w47) }).stdout)
    else
      os.execute("kill " .. G.pid[p.w47])
      G.pid[p.w47] = nil
    end
  else
    return false
  end
  return true
end

-- model commit ids of the new state: a head or tip not seen before is the sha git has there now
local function learn(t, st, G, where)
  local function see(k, sha)
    if G.C[k] then return end
    for j, x in pairs(G.C) do
      if x == sha then error(("%s: commit %d is %s, which is commit %d"):format(where, k, sha, j), 0) end
    end
    G.C[k] = sha
  end
  for i, x in ipairs(st.wts) do
    if x.on and lfs.attributes(G.P[i - 1]) then see(x.head, out(t, G.P[i - 1], "rev-parse", "HEAD")) end  -- else gitcheck says
  end
  for i, k in ipairs(st.brs) do
    local sha = k >= 0 and t:exec({ "git", "-C", t.repo, "rev-parse", "--verify", "-q", "refs/heads/" .. G.BR[i - 1] }).stdout
    if sha and sha ~= "" then see(k, util.strip(sha)) end
  end
end

local function gitcheck(t, st, where, G, N)
  local function fail(what, got, want)
    error(("%s: %s: git has %s, model has %s"):format(where, what, tostring(got), tostring(want)), 0)
  end
  local listed, cur = {}, nil
  for _, l in ipairs(util.splitlines(t:git(t.repo, "worktree", "list", "--porcelain"))) do
    if l:match("^worktree ") then cur = { }; listed[real(l:sub(10))] = cur
    elseif l:match("^HEAD ") then cur.head = l:sub(6)
    elseif l:match("^branch refs/heads/") then cur.br = l:sub(19) end
  end
  local now = util.now()
  for i, x in ipairs(st.wts) do
    local w, p = i - 1, G.P[i - 1]
    local l = p and listed[real(p)]
    if x.on then
      if not l then fail("worktree " .. w, "none", "on") end
      if l.br ~= G.BR[x.br] then fail("worktree " .. w .. " branch", l.br, G.BR[x.br]) end
      if l.head ~= G.C[x.head] then fail("worktree " .. w .. " HEAD", l.head, G.C[x.head]) end
      local st_ = util.strip(t:git(p, "status", "--porcelain"))
      if (st_ ~= "") ~= x.dirty then fail("worktree " .. w .. " dirty", st_, x.dirty) end
      local last = math.max(lfs.attributes(p, "modification") or 0,
        lfs.attributes(out(t, p, "rev-parse", "--absolute-git-dir") .. "/logs/HEAD", "modification") or 0)
      if (now - last < 1800) ~= x.recent then fail("worktree " .. w .. " recent", now - last, x.recent) end
    elseif l or (p and lfs.attributes(p)) then
      fail("worktree " .. w, p, "removed")
    end
  end
  for i, k in ipairs(st.brs) do
    local b = G.BR[i - 1]
    if b then
      local sha = util.strip(t:exec({ "git", "-C", t.repo, "rev-parse", "--verify", "-q", "refs/heads/" .. b }).stdout or "")
      if k >= 0 and sha ~= G.C[k] then fail("branch " .. b, sha, G.C[k]) end
      if k < 0 and sha ~= "" then fail("branch " .. b, sha, "none") end
    end
  end
  for slot, g in pairs(st.ag) do
    if g.st ~= "unborn" and g.st ~= "ended" then
      local r = t:q1("select wt from agent where name=?", N[slot])
      local want = g.wt >= 0 and real(G.P[g.wt]) or nil
      if real(r and r.wt) ~= want then fail("agent " .. N[slot] .. " wt", r and r.wt, want) end
    end
  end
end

-- the name auto-spawn launches next: the failed one the backoff keeps, else m-<the highest number + 1>
local function next_name(t)
  local r = t:q1("select v from meta where k='spawn_backoff'")
  local nm = r and r.v:match("^%d+,%d+,(.+)$")
  if nm then return nm end
  local top = 0
  for _, x in ipairs(t:q("select name from agent")) do
    local n = x.name:match("^m%-(%d+)$")
    if n then top = math.max(top, tonumber(n)) end
  end
  return "m-" .. (top + 1)
end

-- auto-spawn's meta rows against the model's (Spawn.lean's SWorld)
local function spawncheck(t, sp, where)
  if not sp then return end
  local function fail(what, got, want)
    error(("%s: %s: db has %s, model has %s"):format(where, what, tostring(got), tostring(want)), 0)
  end
  local bo = t:q1("select v from meta where k='spawn_backoff'")
  local til = bo and tonumber(bo.v:match("^(%d+)")) or 0
  if (bo ~= nil) ~= sp.bo then fail("spawn_backoff row", bo and bo.v, sp.bo) end
  if (til > util.now()) ~= sp.backoff then fail("spawn_backoff time ahead", bo and bo.v, sp.backoff) end
  local f = t:q1("select v from meta where k='spawn_fails'")
  local want = sp.fails[2] > 0 and ("%d,%d"):format(sp.fails[1], sp.fails[2]) or nil
  if (f and f.v) ~= want then fail("spawn_fails", f and f.v, want) end
  local h = t:q1("select v from meta where k='spawn_halt'")
  want = sp.halt > 0 and tostring(sp.halt) or nil
  if (h and h.v) ~= want then fail("spawn_halt", h and h.v, want) end
end

-- one model action, done to the db the way the code (or the world) does it
local function act(t, name, p, N, G, prev)
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
    local args = { COMMS, "task", "add", "a task" }
    if #p.d28 > 0 then table.insert(args, "--after"); table.insert(args, ids(p.d28)) end
    for id, k in ipairs(prev.task) do  -- the new task is the first absent one; a task on a base other than main says so
      if k.st == "absent" then
        if k.base ~= 0 then table.insert(args, "--base"); table.insert(args, G.BR[k.base]) end
        break
      end
    end
    sw(unpack(args))
  elseif name == "after" then
    if #p.d29 > 0 then sw(COMMS, "task", "after", tostring(p.t29), ids(p.d29))
    else sw(COMMS, "task", "after", tostring(p.t29)) end
  elseif name == "unblock" then sw(COMMS, "task", "unblock", tostring(p.t30), "--answer", "go left")
  elseif name == "drop" then sw(COMMS, "task", "drop", tostring(p.t31))
  elseif name == "tick" then sw(COMMS, "watchd", "--once", "--comms", COMMS, "--max-agents", CAP, "--min-free-mem", "0")
  elseif name == "failExit" then  -- the tick's launch fails: launch.sh exits non-zero
    local f = t.d .. "/launch.fail"
    io.open(f, "w"):close()
    local ok, e = pcall(sw, COMMS, "watchd", "--once", "--comms", COMMS, "--max-agents", CAP, "--min-free-mem", "0")
    os.remove(f)
    if not ok then error(e, 0) end
  elseif name == "failRaise" then  -- launch_agent raises before launch.sh: the new agent's settings file can't be written
    local d = t.d .. "/agents/" .. next_name(t) .. ".settings.json"
    os.remove(d)  -- a launch of that name wrote it before; each launch writes it anew
    os.execute("mkdir -p " .. util.shquote(d))
    local ok, e = pcall(sw, COMMS, "watchd", "--once", "--comms", COMMS, "--max-agents", CAP, "--min-free-mem", "0")
    os.execute("rmdir " .. util.shquote(d))
    if not ok then error(e, 0) end
  elseif name == "lapse" then  -- the backoff's time passes
    setdb(t, "update meta set v=? where k='spawn_backoff'",
      (t:q1("select v from meta where k='spawn_backoff'").v:gsub("^%d+", tostring(now - 1))))
  elseif not gitact(t, name, p, G, hc) then error("no replay for model action " .. name, 0) end
end

local function replay(t, file)
  local text = file:match("%.gz$") and t:exec({ "gzip", "-dc", file }).stdout or util.slurp(file)
  local trace = json.decode(text)
  t:fakes()
  local s0 = trace.states[1].s
  local G = git_setup(t, s0)
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
  gitcheck(t, s0, "init", G, N)
  for i = 2, #trace.states do
    local x = trace.states[i]
    local name, picks = x.action, x.picks
    local where = ("step %d %s %s"):format(i - 1, name, t.repr(picks))
    local ok, err = pcall(act, t, name, picks, N, G, prev)
    if not ok then error(where .. ": " .. tostring(err), 0) end
    local st = x.s
    local M = {}
    for k, n in pairs(N) do M[k] = n end
    -- a spawn: the slot's agent is whoever the db gave its task to. The same tick may end a booting slot's agent
    -- and fill the slot again, so a booting slot is remapped whenever the db's owner differs, if the old one ended.
    -- A launch that raised and was not undone (Spawn.lean's leak) is the same: a row that holds its task, not booting.
    for slot, g in pairs(st.ag) do
      if g.boot or name == "failRaise" then
        for id, k in pairs(st.task) do
          if k.owner == slot and k.st == "claimed" then
            local r = t:q1("select owner, state from task where id=?", id)
            if not (r and r.owner) then
              error(("%s: the model spawned %s for task #%d; the db's is %s with no owner"):format(where, slot, id, r and r.state), 0)
            end
            if r.owner ~= N[slot] then
              local old = N[slot] and (prev.ag[slot].boot or name == "failRaise") and t:q1("select status from agent where name=?", N[slot])
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
    spawncheck(t, st.spawn, where)
    if name == "tick" or name:match("^fail") or name:match("^git") or name:match("^wt") then  -- nothing else changes git or agent.wt
      learn(t, st, G, where)
      gitcheck(t, st, where, G, N)
    end
    prev = st
  end
end

-- ---- PrWatch.lean's layer (board #28): a trace with "pr" replays through the CLI and a fake gh ----
-- The model's tasks are #1.., its agents m-1..; task t's PR is #100+t from branch <owner>/<t> into main, and gh's `pr list`
-- answers what the model has of it. Checked after each step: each task's state and owner, each agent's status, whether
-- an urgent message to it is unread, and whether watchd told it of its PR's current head and verdict (a pr-wake event).
local function replay_pr(t, trace)
  t:fakes()
  t:q("insert or replace into meta(k,v) values('comms',?)", COMMS)
  if trace.pr.gated then
    os.execute("mkdir -p " .. util.shquote(t.repo .. "/.claude"))
    local f = assert(io.open(t.repo .. "/.claude/swarm.json", "w"))
    f:write('{"ci": {"flow": "pr-gated"}}'); f:close()
  end
  local s0 = trace.states[1].s
  for i, g in ipairs(s0.ag) do
    t:agent("m-" .. i)
    t:hook("m-" .. i, "prompt", {})
  end
  for _ = 1, #s0.task do t:sw(COMMS, "task", "add", "a task") end
  local prs, heads = {}, {}  -- task id -> its PR as gh lists it; how many heads it had
  local function gh()
    local l = {}
    for id = 1, #s0.task do if prs[id] then l[#l + 1] = prs[id] end end
    t:set_gh("pr", l)
  end
  local function rollup(v)
    if v == "pending" then return { { __typename = "CheckRun", name = "ci", status = "IN_PROGRESS", conclusion = "" } } end
    return { { __typename = "CheckRun", name = "ci", status = "COMPLETED", conclusion = v == "green" and "SUCCESS" or "FAILURE" } }
  end
  local function iso(x) return os.date("!%Y-%m-%dT%H:%M:%SZ", x) end
  local function sw(who, ...) return t:sw(who, ...) end
  gh()
  local function check(st, where)
    local function fail(what, got, want)
      error(("%s: %s: db has %s, model has %s"):format(where, what, tostring(got), tostring(want)), 0)
    end
    for id, k in ipairs(st.task) do
      local r = t:q1("select state, owner from task where id=?", id)
      if r.state ~= k.st then fail("task #" .. id .. " state", r.state, k.st) end
      if k.st ~= "open" and r.owner ~= k.owner then fail("task #" .. id .. " owner", r.owner, k.owner) end
      local pr = prs[id]
      if pr and pr.state == "OPEN" then
        local key = ("%d %s %s"):format(pr.number, pr.headRefOid, k.pr.checks)
        local told = t:q1("select 1 x from event where kind='pr-wake' and data=?", key) ~= nil
        if told ~= k.pr.told then fail("task #" .. id .. " told (" .. key .. ")", told, k.pr.told) end
      end
    end
    for i, g in ipairs(st.ag) do
      local name = "m-" .. i
      local r = t:q1("select status from agent where name=?", name)
      local want = g.working and "working" or "idle"
      if r.status ~= want then fail("agent " .. name .. " status", r.status, want) end
      local cur = t:q1("select last_msg_id from cursor where agent=?", name)
      local u = t:q1("select count(*) n from msg where id>? and dest=? and urgent=1", cur and cur.last_msg_id or 0, name).n > 0
      if u ~= g.urgent then fail("agent " .. name .. " urgent unread", u, g.urgent) end
    end
  end
  check(s0, "init")
  for i = 2, #trace.states do
    local x = trace.states[i]
    local p, name = x.picks, x.action
    local where = ("step %d %s %s"):format(i - 1, name, t.repr(p))
    local ok, err = pcall(function()
      if name == "claim" then sw(p.a, "task", "claim", tostring(p.t))
      elseif name == "openPr" then
        heads[p.t] = 1
        prs[p.t] = { number = 100 + p.t, headRefName = p.a .. "/" .. p.t, headRefOid = ("h%d-1"):format(p.t),
          baseRefName = "main", state = "OPEN", statusCheckRollup = rollup("pending") }
        gh()
      elseif name == "push" then
        heads[p.t] = heads[p.t] + 1
        prs[p.t].headRefOid = ("h%d-%d"):format(p.t, heads[p.t])
        prs[p.t].statusCheckRollup = rollup("pending")
        gh()
      elseif name == "finish" then prs[p.t].statusCheckRollup = rollup(p.ok and "green" or "red"); gh()
      elseif name == "merge" then
        prs[p.t].state, prs[p.t].mergedAt, prs[p.t].mergeCommit = "MERGED", iso(util.now()), { oid = ("m%d000000"):format(p.t) }
        gh()
      elseif name == "stay" then
        if p.v then sw(p.a, "stay", "CI on its PR, then merge") else sw(p.a, "stay", "--end") end
      elseif name == "stop" then
        t:hook(p.a, "stop", {})
        setdb(t, "update agent set waiter=? where name=?", unistd.getpid(), p.a)
      elseif name == "read" then sw(p.a, "read")
      elseif name == "done" then sw(p.a, "task", "done", tostring(p.t), "--evidence", "abc1234")
      elseif name == "poll" then
        setdb(t, "delete from meta where k='pr_watched'")  -- a minute has passed
        sw(COMMS, "watchd", "--once", "--ci", "--comms", COMMS, "--max-agents", CAP, "--min-free-mem", "0")
      elseif name == "wake" then
        local r = sw(p.a, "wait", "--timeout", "5", "--poll", "0.1", { ok = false })
        if r.code ~= 2 then error(("swarm wait exited %d, the model woke it: %s"):format(r.code, r.stderr), 0) end
        t:hook(p.a, "prompt", {})
      else error("no replay for PrWatch action " .. name, 0) end
    end)
    if not ok then error(where .. ": " .. tostring(err), 0) end
    check(x.s, where)
  end
end

local T = {}
if lfs.attributes(DIR, "mode") == "directory" then
  for f in lfs.dir(DIR) do
    if f:match("%.json$") or f:match("%.json%.gz$") then
      T["trace " .. f] = function(t)
        t.repr = require("test.cli").repr
        local file = DIR .. "/" .. f
        local text = file:match("%.gz$") and t:exec({ "gzip", "-dc", file }).stdout or util.slurp(file)
        local trace = json.decode(text)
        if trace.pr then replay_pr(t, trace) else replay(t, file) end
      end
    end
  end
end
return T
