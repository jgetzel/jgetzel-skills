-- Differential tests of swarm/model/SwarmModel/Env.lean's sqlite assumptions (board #33): Iso.lean's engine against
-- real sqlite, through db.lua (WAL, busy_timeout 10 s, db:tx is begin immediate), many processes at once. Each case
-- carries the name its hypothesis's tag gives (sqlite_begin, sqlite_read, sqlite_write, sqlite_commit, sqlite_rollback); check.sh
-- refuses an assumption with no case here or in env_spec.lua. No connection is open across a fork: each child opens
-- its own.
local db, ptime = require "swarm.db", require "posix.time"
local stdlib, unistd, signal, wait = require "posix.stdlib", require "posix.unistd", require "posix.signal",
  require "posix.sys.wait"
local d = stdlib.mkdtemp((os.getenv("TMPDIR") or "/tmp") .. "/swarm-sqlite-XXXXXX")
local function secs() local t = ptime.clock_gettime(ptime.CLOCK_MONOTONIC); return t.tv_sec + t.tv_nsec / 1e9 end
stdlib.setenv("SWARM_DB", d .. "/sq/swarm.db")
local c = db.connect()
c:script("create table ctr(k text primary key, v int); create table seen(v int); create table acct(id int primary key, bal int)")
c:exec("insert into ctr values('tx',0),('auto',0)")
for i = 1, 8 do c:exec("insert into acct values(?,100)", i) end
c.h:close()
local function child(fn)  -- a process running fn on its own connection: exit 0 if it returns
  local p = unistd.fork()
  if p == 0 then
    local ok, e = pcall(function() fn(db.connect()) end)
    if not ok then io.stderr:write("env_spec child: ", tostring(type(e) == "table" and e.exit or e), "\n") end
    unistd._exit(ok and 0 or 1)
  end
  return p
end
local function failed(pids)
  local n = 0
  for _, p in ipairs(pids) do if select(3, wait.wait(p)) ~= 0 then n = n + 1 end end
  return n
end
-- Counters (6 processes): in db:tx read the counter, write it +1, read it back, log the value read; outside a
-- transaction add one to another. Transfers (3): move 1 between two of 8 accounts in db:tx. Readers (3): the sum.
local N, K, pids = 6, 150, {}
for _ = 1, N do pids[#pids + 1] = child(function(x)
  for _ = 1, K do
    x:tx(function()
      local v = x:one("select v from ctr where k='tx'").v
      x:exec("update ctr set v=? where k='tx'", v + 1)
      assert(x:one("select v from ctr where k='tx'").v == v + 1, "sqlite_read: a transaction reads its own writes")
      x:exec("insert into seen(v) values(?)", v)
    end)
    x:exec("update ctr set v=v+1 where k='auto'")
  end
end) end
for i = 1, 3 do pids[#pids + 1] = child(function(x)
  math.randomseed(i)
  for _ = 1, K do
    local a, b = math.random(8), math.random(8)
    x:tx(function()
      x:exec("update acct set bal=bal-1 where id=?", a)
      x:exec("update acct set bal=bal+1 where id=?", b)
    end)
  end
end) end
for _ = 1, 3 do pids[#pids + 1] = child(function(x)
  for _ = 1, 4 * K do
    local r = x:one("select sum(bal) s, count(*) n from acct")
    assert(r.s == 800 and r.n == 8, "sqlite_read, sqlite_commit: a read saw part of a transaction")
  end
end) end
assert(failed(pids) == 0, "sqlite_begin, sqlite_write, sqlite_commit: no process fails (each waits within busy_timeout)")
c = db.connect()
assert(c:one("select v from ctr where k='tx'").v == N * K, "sqlite_begin: no update in a transaction is lost")
assert(c:one("select v from ctr where k='auto'").v == N * K, "sqlite_write: no update outside a transaction is lost")
local r = c:one("select count(*) n, count(distinct v) dv, min(v) lo, max(v) hi from seen")
assert(r.n == N * K and r.dv == N * K and r.lo == 0 and r.hi == N * K - 1,
  "sqlite_begin: each transaction read the latest counter, and no two the same")
c.h:close()

-- A holder keeps the write lock 1 s (begin immediate, a write). Another connection, busy_timeout 0.2 s: begin
-- immediate and a write outside a transaction wait it out and fail, changing nothing and leaving no transaction open;
-- its reads don't wait and don't see the holder's write; a long reader doesn't hold up a commit (WAL).
local rd, wr = unistd.pipe()
local holder = unistd.fork()
if holder == 0 then
  local x = db.connect()
  x:script("begin immediate"); x:exec("update ctr set v=-1 where k='auto'")
  unistd.write(wr, "x"); unistd.sleep(1)
  x:script("commit")
  unistd._exit(0)
end
unistd.read(rd, 1)
c = db.connect()
c.h:busy_timeout(200)
local t0 = secs()
local ok, e = pcall(c.tx, c, function() c:exec("insert into seen(v) values(-1)") end)
assert(not ok and tostring(e):find("locked") and secs() - t0 >= 0.19, "sqlite_begin: waits out busy_timeout, then SQLITE_BUSY")
t0 = secs()
ok, e = pcall(c.exec, c, "update ctr set v=v+1 where k='auto'")
assert(not ok and tostring(e):find("locked") and secs() - t0 >= 0.19, "sqlite_write: waits out busy_timeout, then SQLITE_BUSY")
t0 = secs()
assert(c:one("select v from ctr where k='auto'").v == N * K and secs() - t0 < 0.1,
  "sqlite_read: a read doesn't wait on the writer and doesn't see its uncommitted write")
assert(select(3, wait.wait(holder)) == 0)
c.h:busy_timeout(10000)
c:tx(function() end)  -- no transaction was left open by the BUSYs (else: cannot start a transaction within a transaction)
assert(c:one("select v from ctr where k='auto'").v == -1, "sqlite_commit: the holder's commit is the next version")
assert(c:one("select count(*) n from seen where v=-1").n == 0, "sqlite_begin: a BUSY changes nothing")
c.h:close()
rd, wr = unistd.pipe()
local reader = unistd.fork()
if reader == 0 then
  local x = db.connect()
  x:script("begin"); x:one("select count(*) n from acct")  -- a read transaction, held open
  unistd.write(wr, "x"); unistd.sleep(1)
  x:script("commit")
  unistd._exit(0)
end
unistd.read(rd, 1)
c = db.connect()
c.h:busy_timeout(200)
t0 = secs()
c:tx(function() c:exec("update ctr set v=0 where k='auto'") end)
assert(secs() - t0 < 0.15, "sqlite_commit: a commit doesn't wait for a reader (WAL)")
assert(select(3, wait.wait(reader)) == 0)

-- Iso.not_busyClean_deferred on real sqlite: a deferred transaction that has read, then writes after another
-- connection's commit, gets SQLITE_BUSY (BUSY_SNAPSHOT) at once, busy_timeout (10 s) not waited, and stays open.
local a, b = db.connect(), db.connect()
a:script("begin"); a:one("select v from ctr where k='auto'")
b:exec("update ctr set v=v+1 where k='auto'")
t0 = secs()
ok, e = pcall(a.exec, a, "update ctr set v=v+1 where k='auto'")
assert(not ok and tostring(e):find("locked") and secs() - t0 < 1, "deferred: SQLITE_BUSY at once")
assert(not pcall(a.script, a, "begin"), "deferred: the transaction stays open after it")
a:script("rollback")
a.h:close(); b.h:close(); c.h:close()

-- A transaction whose process is killed (SIGKILL) in it, or whose db:tx function errors, leaves nothing and frees the lock.
rd, wr = unistd.pipe()
local victim = unistd.fork()
if victim == 0 then
  local x = db.connect()
  x:script("begin immediate"); x:exec("insert into seen(v) values(-7)")
  unistd.write(wr, "x"); unistd.sleep(30)
  unistd._exit(0)
end
unistd.read(rd, 1)
signal.kill(victim, signal.SIGKILL); wait.wait(victim)
c = db.connect()
c.h:busy_timeout(1000)
c:tx(function() end)  -- the lock is free
assert(not pcall(c.tx, c, function() c:exec("insert into seen(v) values(-8)"); error("no") end))
assert(c:one("select count(*) n from seen where v in (-7, -8)").n == 0, "sqlite_rollback: nothing of either is left")
assert(c:one("pragma integrity_check").integrity_check == "ok")
c.h:close()

os.execute("rm -rf " .. d)
