-- db: integral numbers stay integers in text columns, tx rolls back on die, the task.after migration.
local util, db = require "swarm.util", require "swarm.db"
local stdlib = require "posix.stdlib"
local dir = stdlib.mkdtemp((os.getenv("TMPDIR") or "/tmp") .. "/swarm-spec-XXXXXX")
stdlib.setenv("SWARM_DB", dir .. "/sub/swarm.db")
local c = db.connect()

c:exec("insert into meta(k,v) values(?,?)", "n", 1794)
c:exec("insert into meta(k,v) values(?,?)", "neg", -5)
c:exec("insert into meta(k,v) values(?,?)", "f", 4.85)
c:exec("insert into meta(k,v) values(?,?)", "q?'x'", "it's ?")
assert(c:one("select v from meta where k='n'").v == "1794")  -- not '1794.0': Python int()s it
assert(c:one("select v from meta where k='neg'").v == "-5" and c:one("select v from meta where k='f'").v == "4.85")
assert(c:one("select v, typeof(v) t from meta where k=?", "q?'x'").v == "it's ?")
assert(c:one("select 10-? x", -5).x == 15)  -- a negative literal is parenthesized, not `--`
assert(c:one("select ? x", nil).x == nil and c:one("select ? x", true).x == 1)
assert(c:one("select 1 from meta where k='a''?b'") == nil)  -- a ? inside a literal is not a parameter
assert(c:exec("update meta set v='z' where k like ?", "%") == 4)

-- die inside tx rolls back and goes on up as {exit = code}; nested tx joins the outer one
local ok, e = pcall(c.tx, c, function()
  c:exec("insert into meta(k,v) values('gone','1')")
  c:tx(function() c:exec("insert into meta(k,v) values('gone2','1')") end)
  util.die("no", 3)
end)
assert(not ok and e.exit == 3 and c.depth == 0)
assert(c:one("select count(*) n from meta where k like 'gone%'").n == 0)
assert(c:tx(function() return 7, nil, 9 end) == 7)
assert(select(3, c:tx(function() return 7, nil, 9 end)) == 9)
assert(not pcall(c.exec, c, "insert into nope values(1)"))
assert(not pcall(c.exec, c, "select ?, ?", 1))

-- a second connection holding `begin immediate` makes a write wait for it (busy_timeout), then succeed
-- (exercised by test_concurrent_lock_waits_not_double_writes against the CLI)

-- an old db with task.after: copied into deps, column dropped
c.h:exec("alter table task add column after int")
c:exec("insert into task(title, after) values('t', 3)")
c.h:close()
c = db.connect()
assert(not c:columns("task").after and c:one("select deps from task").deps == "3")
for _, tc in ipairs(db.COLUMNS) do assert(c:columns(tc[1])[tc[2]:match("^%S+")], tc[2]) end
db.log(c, "a", "join")
local ev = c:one("select * from event")
assert(ev.agent == "a" and ev.kind == "join" and ev.path == nil and ev.ts >= util.now() - 5)
c.h:close()
os.execute("rm -rf '" .. dir .. "'")
