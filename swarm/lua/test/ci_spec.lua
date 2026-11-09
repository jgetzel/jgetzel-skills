-- ci: pr_ci merge-to-green, ci_poll's one request and backoff, ci_check's one red task closed by green. A fake gh on PATH.
local db, ci, json = require "swarm.db", require "swarm.ci", require "swarm.json"
local stdlib, unistd = require "posix.stdlib", require "posix.unistd"
local dir = stdlib.mkdtemp((os.getenv("TMPDIR") or "/tmp") .. "/swarm-spec-XXXXXX")
os.execute("mkdir " .. dir .. "/bin; cd " .. dir .. " && git init -q . && git -c user.name=t -c user.email=t@t commit -q --allow-empty -m 'x" ..
  "\n\nSwarm-Agent: a' && git -c user.name=t -c user.email=t@t commit -q --allow-empty -m 'y\n\nSwarm-Agent: gone'")
local function gh(api, pr)  -- what the fake answers; every call is logged
  local f = io.open(dir .. "/bin/gh", "w")
  f:write("#!/bin/sh\necho \"$@\" >> " .. dir .. "/calls\ncase \"$1\" in api) cat " .. dir .. "/api;; pr) cat " .. dir
    .. "/pr;; *) echo 'step Build failed';; esac\n")
  f:close()
  os.execute("chmod +x " .. dir .. "/bin/gh")
  for k, v in pairs({ api = api, pr = pr }) do
    f = io.open(dir .. "/" .. k, "w"); f:write(v or ""); f:close()
  end
end
local function calls(pat)
  local n = 0
  for l in io.lines(dir .. "/calls") do if l:find(pat) then n = n + 1 end end
  return n
end
stdlib.setenv("PATH", dir .. "/bin:" .. os.getenv("PATH"))
stdlib.setenv("SWARM_DB", dir .. "/swarm.db")
local c = db.connect()
io.open(dir .. "/calls", "w"):close()

assert(ci.ts("1970-01-02T00:00:01Z") == 86401 and ci.ts("2000-03-01T00:00:00Z") == 951868800)

-- pr_ci
c:exec("insert into agent(name,started) values('a',1)")
c:exec("insert into task(title,state,owner,evidence,done_at,first_claimed_at) values('t1','done','a','PR #7 merged',?,1)", os.time())
c:exec("insert into ci(id,sha,status,conclusion,created,updated) values(1,'red','completed','failure','2026-11-08T10:00:05Z','2026-11-08T10:02:00Z')")
c:exec("insert into ci(id,sha,status,conclusion,created,updated) values(2,'fix','completed','success','2026-11-08T10:05:00Z','2026-11-08T10:08:00Z')")
gh("", '[{"number":7,"mergedAt":"2026-11-08T10:00:00Z","mergeCommit":{"oid":"red"},"headRefName":"a/x"}]')
ci.pr_ci(c, dir)
local t = c:one("select pr, merged_at, ci_conclusion, ci_green_at from task where id=1")
assert(t.pr == 7 and t.ci_conclusion == "failure" and t.ci_green_at - t.merged_at == 480, json.encode(t))
ci.pr_ci(c, dir)
assert(calls("^pr ") == 1)  -- the PR list is asked for at most every 10 minutes

-- ci_poll: one request for the runs, one for the red run's jobs; within the minute no call; refused keeps the table
c:exec("delete from ci")
gh('[{"databaseId":1,"headSha":"a1","status":"completed","conclusion":"failure","url":"u1","createdAt":"2026-11-08T10:00:00Z","updatedAt":"2026-11-08T10:03:00Z","event":"push"}]')
ci.ci_poll(c, dir)
assert(calls("^api") == 1 and calls("%-%-json jobs") == 1 and calls("event=push") == 1)  -- a scheduled run isn't CI
assert(c:one("select failed from ci where id=1").failed == "step Build failed")
ci.ci_poll(c, dir)
assert(calls("^api") == 1)
c:exec("update meta set v='0' where k='ci_polled'")
gh("")
ci.ci_poll(c, dir)
assert(c:one("select count(*) n from ci").n == 1 and c:one("select 1 from meta where k='ci_error'"))

-- ci_check: one red task naming the live suspect, a later red joins it, green closes it and tells the fixer
local function sha(n) return (io.popen("git -C " .. dir .. " rev-parse HEAD~" .. n):read("*l")) end
local red = sha(0)
c:exec("delete from ci"); c:exec("delete from meta"); c:exec("delete from task")
c:exec("insert into ci(id,sha,status,conclusion,url,created) values(9,?, 'completed','failure','http://ci/9','2026-11-08T10:05:00Z')", red)
ci.ci_check(c, dir, "comms")
ci.ci_check(c, dir, "comms")  -- edge-triggered
assert(c:one("select count(*) n from task where title like 'main red:%'").n == 1)
local tid = c:one("select id from task").id
local m = c:all("select dest, body from msg where kind='system'")
assert(#m == 1 and m[1].dest == "a" and m[1].body:find("http://ci/9") and m[1].body:find("swarm task claim " .. tid), json.encode(m))
c:exec("insert into ci(id,sha,status,conclusion,url,created) values(10,?, 'completed','failure','u','2026-11-08T10:10:00Z')", red)
ci.ci_check(c, dir, "comms")
assert(c:one("select count(*) n from task").n == 1 and c:one("select body from task where id=" .. tid .. "").body:find("Later red: run 10"))
c:exec("update task set state='claimed', owner='a' where id=" .. tid .. "")
c:exec("update ci set status='in_progress', conclusion=null where id=10")  -- a re-run: the older red is not on top
ci.ci_check(c, dir, "comms")
assert(c:one("select state from task where id=" .. tid .. "").state == "claimed")
c:exec("insert into ci(id,sha,status,conclusion,url,created) values(11,?, 'completed','success','u','2026-11-08T10:20:00Z')", red)
ci.ci_check(c, dir, "comms")
local d = c:one("select state, evidence from task where id=" .. tid .. "")
assert(d.state == "done" and d.evidence == "green run 11 at " .. red:sub(1, 7), json.encode(d))
assert(c:one("select body from msg where dest='a' order by id desc limit 1").body:find("is done; stop fixing it"))
-- no live suspect: comms hears
c:exec("update agent set ended=1"); c:exec("delete from event where kind='ci-red'"); c:exec("delete from ci")
c:exec("insert into ci(id,sha,status,conclusion,url,created) values(9,?, 'completed','failure','http://ci/9','2026-11-08T10:05:00Z')", red)
ci.ci_check(c, dir, "comms")
assert(c:one("select count(*) n from msg where dest='comms'").n == 1)

-- a scheduled (or other) workflow's green run on the red sha: not main's CI, so the red task stays and ci reads red
c:exec("delete from ci"); c:exec("delete from task"); c:exec("delete from event where kind='ci-red'")
c:exec("delete from meta"); os.execute("mkdir -p " .. dir .. "/.claude")
local f = io.open(dir .. "/.claude/swarm.json", "w"); f:write('{"ci": {"workflow": "ci.yml"}}'); f:close()
local function run(id, concl, event, wf, at)
  return { databaseId = id, headSha = red, status = "completed", conclusion = concl, url = "u", createdAt = at,
    updatedAt = at, event = event, workflow = wf, path = ".github/workflows/" .. wf .. ".yml" }
end
c:exec("insert into ci(id,sha,status,conclusion,created) values(5,'old','completed','success','2026-11-08T09:00:00Z')")  -- pre-filter row
gh(json.encode({ run(22, "success", "push", "deploy", "2026-11-08T11:02:00Z"),  -- push, but not ci.workflow
  run(21, "success", "schedule", "ci", "2026-11-08T11:01:00Z"), run(20, "failure", "push", "ci", "2026-11-08T11:00:00Z") }))
ci.ci_poll(c, dir)
ci.ci_check(c, dir, "comms")
local rows = c:all("select id, workflow from ci")
assert(#rows == 1 and rows[1].id == 20 and rows[1].workflow == "ci", json.encode(rows))
assert(c:one("select count(*) n from task where title like 'main red: run 20%' and state='open'").n == 1)
assert(ci.ci_for(c, red, dir) == "failure")
