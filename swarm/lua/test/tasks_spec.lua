-- tasks: reserve claims for a new agent, a lost race raises {lost}, unreserve reopens; event_task parses ids.
local db, tasks = require "swarm.db", require "swarm.tasks"
local stdlib = require "posix.stdlib"
local dir = stdlib.mkdtemp((os.getenv("TMPDIR") or "/tmp") .. "/swarm-spec-XXXXXX")
stdlib.setenv("SWARM_DB", dir .. "/swarm.db")
local c = db.connect()

assert(tasks.event_task({ data = "#12 title" }) == 12 and tasks.event_task({ data = "auto #3" }) == 3)
assert(tasks.event_task({ data = "#12x" }) == nil and tasks.event_task({ data = "t-3" }) == nil)

c:exec("insert into task(title) values('one')")
c:exec("insert into task(title,deps) values('two','1')")
local ok, e = pcall(tasks.reserve, c, "n1", 2, "sonnet")  -- waits on #1
assert(not ok and e.exit == 1 and not e.lost)
local r = tasks.reserve(c, "n1", 1, "sonnet")
assert(r.title == "one")
local t = c:one("select state, owner, first_claimed_at from task where id=1")
assert(t.state == "claimed" and t.owner == "n1" and t.first_claimed_at)
assert(c:one("select model from agent where name='n1'").model == "sonnet")

ok, e = pcall(tasks.reserve, c, "n2", 1)  -- a peer got it first
assert(not ok and e.lost == "task #1 is claimed, owned by n1", tostring(e.lost))

tasks.unreserve(c, "n1", r)
t = c:one("select state, owner, first_claimed_at from task where id=1")
assert(t.state == "open" and t.owner == nil and t.first_claimed_at == nil)
assert(c:one("select ended from agent where name='n1'").ended)

-- task claim's dependency check holds in its write: a `task after` that lands between claim's read of the deps
-- and its update must not let the task start (found by swarm/model: s2_racy, noEarlyStart)
c:exec("insert into task(title) values('three')")  -- #3, open, no deps; #2 waits on #1, which n1 lost above
stdlib.setenv("SWARM_NAME", "n3")
local raced = setmetatable({ exec = function(self, sql, ...)
  if sql:find("^update task set state='claimed'") then c:exec("update task set deps='1' where id=3") end
  return c.exec(c, sql, ...)
end }, { __index = function(_, k) local f = c[k]; return type(f) == "function" and function(_, ...) return f(c, ...) end or f end })
ok, e = pcall(tasks.cmd_task, raced, { act = "claim", id = 3, lease = "2h" })
assert(not ok and e.exit == 1, "claimed #3 while #1 it now waits on is open")
assert(c:one("select state from task where id=3").state == "open")
