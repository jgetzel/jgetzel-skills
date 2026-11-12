-- watchd races (test_swarm.py's racing() proxy as a patched c.all): a peer writes between a read and the write that
-- depends on it, and the write must not clobber it. Plus end_agent's re-check and auto-spawn's lost race.
local db, tasks, watchd, agents, proc = require "swarm.db", require "swarm.tasks", require "swarm.watchd", require "swarm.agents",
  require "swarm.proc"
local stdlib, unistd = require "posix.stdlib", require "posix.unistd"
local dir = stdlib.mkdtemp((os.getenv("TMPDIR") or "/tmp") .. "/swarm-spec-XXXXXX")
local repo = dir .. "/repo"
assert(proc.run({ "git", "init", "-q", "-b", "main", repo }))
assert(proc.run({ "git", "-C", repo, "-c", "user.name=t", "-c", "user.email=t@t", "commit", "-q", "--allow-empty", "-m", "init" }))
local home = unistd.getcwd()
assert(unistd.chdir(repo))
stdlib.setenv("SWARM_DB", dir .. "/swarm.db")
stdlib.setenv("SWARM_NAME", "a")
stdlib.setenv("HC_TERMINAL_ID", nil)
local peer = db.connect()

local function fresh()  -- an empty board and a connection of our own
  for _, t in ipairs({ "agent", "task", "lock", "event", "msg", "cursor", "meta" }) do peer:exec("delete from " .. t) end
  peer:exec("delete from sqlite_sequence")
  return db.connect()
end

-- c, but fn runs once right after the first query containing frag has read its rows: a peer acting in between.
local function racing(c, frag, fn)
  local all = c.all
  c.all = function(self, sql, ...)
    local rows = all(self, sql, ...)
    if fn and sql:find(frag, 1, true) then
      local f = fn
      fn = nil
      f()
    end
    return rows
  end
  return c
end

local function claim(name, title)  -- what `swarm join` then `task add` + `task claim` leave
  local t = os.time()
  peer:exec("insert or ignore into agent(name,cwd,status,last_active,started,hc) values(?,?,'idle',?,?,?)", name, repo, t, t,
    os.getenv("HC_TERMINAL_ID"))
  peer:exec("insert into task(title,state,owner,lease_until) values(?,'claimed',?,?)", title, name, t + 7200)
end

local function task1() return peer:one("select state, owner from task where id=1") end

-- reap judged a dead from hc ls (bound to t1, only t2 live), but a takeover rebound it to t2 since: spared
local c = fresh()
claim("a", "t")
peer:exec("update agent set hc='t1'")
local out = watchd.reap(racing(c, "from agent where ended is null", function() peer:exec("update agent set hc='t2' where name='a'") end),
  { t2 = true })
assert(#out == 0, table.concat(out, ","))
local a = peer:one("select hc, ended from agent")
assert(a.hc == "t2" and a.ended == nil)
assert(task1().state == "claimed")

-- a renew after reap's select of expired leases keeps the task; a fresh lock after its lock select keeps the lock
c = fresh()
claim("a", "t1")
peer:exec("insert into lock(path,agent,since,lease_until) values('a.txt','a',1,?)", os.time() + 3600)
peer:exec("update task set lease_until=1")
peer:exec("update agent set ended=1")
out = watchd.reap(racing(c, "from task where state='claimed'", function()
  peer:exec("update task set lease_until=? where id=1", os.time() + 3600)
end))
assert(#out == 0, table.concat(out, ","))
assert(task1().state == "claimed")
peer:exec("update lock set lease_until=1")
out = watchd.reap(racing(db.connect(), "select * from lock", function() peer:exec("update lock set lease_until=?", os.time() + 3600) end))
assert(#out == 0, table.concat(out, ","))
assert(#peer:all("select * from lock") == 1)

-- done/renew/block/release by a after its task was reaped and reclaimed by b: refused, b keeps it
c = fresh()
claim("a", "t1")
for _, act in ipairs({ "done", "renew", "block", "release" }) do
  local rc = racing(db.connect(), "select * from task where id=?", function() peer:exec("update task set owner='b' where id=1") end)
  local ok, e = pcall(tasks.cmd_task, rc, { act = act, id = 1, evidence = "e", lease = "1h", question = "q" })
  assert(not ok and type(e) == "table" and e.exit, act .. ": " .. tostring(e))
  local t = task1()
  assert(t.state == "claimed" and t.owner == "b", act)
  peer:exec("update task set owner='a'")
end

-- end_agent re-checks what lifecycle judged: e claimed a task since, so it is neither ended nor cleaned
c = fresh()
peer:exec("insert into agent(name,cwd,status,last_active,started) values('e',?,'idle',1,1)", repo)
local row = c:one("select * from agent where name='e'")
peer:exec("insert into task(title,state,owner,lease_until) values('t','claimed','e',?)", os.time() + 3600)
local run = proc.run
proc.run = function() return nil end
watchd.end_agent(c, row)
proc.run = run
assert(peer:one("select ended from agent where name='e'").ended == nil)
assert(task1().owner == "e")

-- end_agent re-checks stay: e ran `swarm stay` between lifecycle's judgment and the end, so it is kept
c = fresh()
peer:exec("insert into agent(name,cwd,status,last_active,started) values('e',?,'idle',1,1)", repo)
row = c:one("select * from agent where name='e'")
peer:exec("update agent set stay='reviews' where name='e'")
proc.run = function() return nil end
watchd.end_agent(c, row)
proc.run = run
assert(peer:one("select ended from agent where name='e'").ended == nil)

-- end_agent kills what the agent left in its cgroup scope
c = fresh()
local machine = require "swarm.machine"
local pr, cg0 = machine.PROC, machine.CGROUP
machine.PROC, machine.CGROUP = dir .. "/proc", dir .. "/cg"
os.execute(("mkdir -p %s/proc/77 %s/cg/u/swarm-agent-e-1.scope"):format(dir, dir))
os.execute(("echo '0::/u/swarm-agent-e-1.scope' > %s/proc/77/cgroup; echo 1048576 > %s/cg/u/swarm-agent-e-1.scope/memory.peak"):format(dir, dir))
peer:exec("insert into agent(name,cwd,status,last_active,started,claude_pid) values('e',?,'idle',1,1,77)", repo)
row = c:one("select * from agent where name='e'")
proc.run = function() return nil end
watchd.end_agent(c, row)
proc.run = run
machine.PROC, machine.CGROUP = pr, cg0
assert(peer:one("select ended from agent where name='e'").ended ~= nil)
assert(require("swarm.util").slurp(dir .. "/cg/u/swarm-agent-e-1.scope/cgroup.kill") == "1")

-- auto-spawn: a peer claims the task between pool() and the reserve; nothing launches, the peer keeps it
c = fresh()
peer:exec("insert into agent(name,cwd,status,last_active,started) values('t-comms',?,'working',1,1)", repo)
peer:exec("insert into task(title) values('do it')")
local launched, pool, hc = {}, tasks.pool, agents.hc_terminals
stdlib.setenv("SWARM_LAUNCH", dir .. "/launch")
proc.run = function(argv, ...)
  if argv[1] == dir .. "/launch" then launched[#launched + 1] = argv; return "hc1" end
  return run(argv, ...)
end
agents.hc_terminals = function() return nil end
tasks.pool = function(cc)
  local r = pool(cc)
  peer:exec("insert into agent(name,cwd,status,last_active,started) values('t-1',?,'working',1,1)", repo)
  peer:exec("update task set state='claimed', owner='t-1' where id=1")
  return r
end
-- cap 2: with t-1 live there is room for t-2, so the spawn is tried and its reserve loses (cap 1 would stop before it)
peer:exec("insert or replace into meta(k,v) values('agent_min','2')")
watchd.watchd_tick(c, "t-comms", nil, { min_free_gib = 0 })
proc.run, tasks.pool, agents.hc_terminals = run, pool, hc
assert(#launched == 0)
assert(task1().owner == "t-1")
assert(not peer:one("select 1 from agent where name='t-2'"))
assert(not peer:one("select 1 from msg where dest='t-comms'"))  -- a lost race is no launch failure

-- board #84: each pass under its own pcall: reap failing ends reap alone; the notices still run, and the tick raises it
do
  c = fresh()
  peer:exec("insert into task(title,state,owner,question) values('q','blocked','x','which way?')")
  local reap, hc = watchd.reap, agents.hc_terminals
  watchd.reap, agents.hc_terminals = function() error("boom", 0) end, function() return nil end
  local ok, err = pcall(watchd.watchd_tick, c, "t-comms", nil, { min_free_gib = 0 })
  watchd.reap, agents.hc_terminals = reap, hc
  assert(not ok and tostring(err):find("reap: boom", 1, true), tostring(err))
  assert(peer:one("select 1 from msg where dest='t-comms' and body like '%is blocked on #1%'"))
  assert(peer:one("select 1 from event where kind='task-blocked' and path='1'"))
end

unistd.chdir(home)
proc.run({ "rm", "-rf", dir })

-- the whole iteration is under pcall: an error in a pass that was not wrapped (ci_poll) used to end watchd, and so did
-- one in the loop's own read of the record
do
  local ci = require "swarm.ci"
  local real = ci.ci_poll
  ci.ci_poll = function() error("boom") end
  local c2 = db.connect()
  c2:exec("insert or replace into meta(k,v) values('watchd','me')")
  local opts = { min_free_gib = 0, once = true }
  assert(select(2, watchd.loop(c2, "me", "t-comms", "/nonexistent", opts)) == false)
  assert(select(2, watchd.loop(c2, "me", "t-comms", "/nonexistent", opts)) == false)
  assert(#c2:all("select 1 from event where kind='watchd-tick-error'") == 1)  -- once per distinct message
  ci.ci_poll = real
  assert(select(2, watchd.loop(c2, "me", "t-comms", nil, opts)) == true)
  assert(c2:one("select v from meta where k='watchd_up'").v == "me")
  local gone = setmetatable({}, { __index = function() error("database is locked") end })
  local why, up = watchd.loop(gone, "me", "t-comms", nil, opts)
  assert(why == nil and up == false)
end
