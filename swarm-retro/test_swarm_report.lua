-- swarm-report driven through its CLI, on a db built by `swarm` itself and filled with fixture rows.
-- Run: luajit swarm-retro/test_swarm_report.lua (needs swarm's rocks). A spec passes by returning; a failed assert dies.
local here = arg[0]:match("^(.*)/[^/]*$") or "."
if here:sub(1, 1) ~= "/" then here = require("lfs").currentdir() .. "/" .. here end  -- the report runs from a temp cwd
local tree = (os.getenv("XDG_DATA_HOME") or ((os.getenv("HOME") or "") .. "/.local/share")) .. "/swarm/lua"
package.path = here .. "/../swarm/lua/?.lua;" .. tree .. "/share/lua/5.1/?.lua;" .. tree .. "/share/lua/5.1/?/init.lua;" .. package.path
package.cpath = tree .. "/lib/lua/5.1/?.so;" .. package.cpath
local sqlite3, stdlib = require "lsqlite3", require "posix.stdlib"
local json, proc = require "swarm.json", require "swarm.proc"
local REPORT, SWARM = here .. "/swarm-report", here .. "/../swarm/swarm"
local NOGIT = { GIT_DIR = "/nonexistent" }  -- no history, no gh

local function tmp() return stdlib.mkdtemp((os.getenv("TMPDIR") or "/tmp") .. "/report-test-XXXXXX") end
local function sh(cmd) assert(os.execute(cmd) == 0, cmd) end
local function merge(a, b) local o = {}; for _, t in ipairs({ a, b or {} }) do for k, v in pairs(t) do o[k] = v end end; return o end

-- Report (as json) on a fresh db after running the sql.
local function run(sql, o)
  o = o or {}
  local d = tmp()
  local env = merge({ SWARM_DB = d .. "/swarm.db", SWARM_NAME = "t", HOME = o.home or d }, o.env)
  local _, err, code = proc.exec({ SWARM, "task", "add", "seed" }, { env = env })  -- makes the schema
  assert(code == 0, tostring(code) .. " " .. err)
  local c = assert(sqlite3.open(d .. "/swarm.db"))
  assert(c:exec("delete from task; delete from event;" .. (sql or "")) == sqlite3.OK, c:errmsg())
  c:close()
  local out, err2, code2 = proc.exec({ REPORT, "--json", unpack(o.args or {}) }, { env = env, cwd = o.cwd or d })
  assert(code2 == 0, tostring(code2) .. " " .. err2)
  return json.decode(out)
end
local function eq(a, b) assert(json.encode(a) == json.encode(b), json.encode(a) .. " ~= " .. json.encode(b)) end
local function kinds(l) local o = {}; for i, e in ipairs(l) do o[i] = e.kind end; return o end

local T = {}

function T.claim_to_done()
  local r = run([[insert into task(id,title,state,owner,evidence) values(1,'t','done','a','sha');
insert into event(ts,agent,kind,data) values(100,'a','claim','#1 t'),(190,'a','done','#1 sha'),(150,'a','reap','x'),(160,'a','digest',null);]],
    { env = NOGIT })
  assert(r.tasks[1].took == "1m30s" and r.friction[1].kind == "reap" and #r.idle_with_open_tasks == 1)
end

function T.task_durations_from_events()
  local r = run([[insert into task(id,title,state,owner,evidence) values(1,'t','done','b','sha');
insert into event(ts,agent,kind,data) values(10,'a','task-add','#1 t'),(100,'a','claim','#1 t'),(130,'a','block','#1 q'),(160,'a','unblock','#1'),
 (200,'a','release','#1'),(300,'b','claim','#1 t'),(400,'b','done','#1 sha');]], { env = NOGIT })
  local t = r.tasks[1]
  eq({ t.queue_wait_s, t.work_s, t.total_s, t.blocked_s, t.claims, t.releases, t.holders }, { 90, 300, 390, 30, 2, 1, { "a", "b" } })
  assert(r.task_durations.work_median_s == 300 and r.task_durations.reclaimed[1].id == 1)
end

function T.conflict_events()
  local r = run([[insert into event(ts,agent,kind,path,data) values(1,'a','conflict','L.hs','b'),(2,'a','conflict-compat',null,'b'),(3,'b','shared-tree','/r','a');]],
    { env = NOGIT })
  eq(kinds(r.conflicts), { "conflict", "conflict-compat", "shared-tree" })
  eq(kinds(r.friction), { "conflict", "shared-tree" })  -- compat is not friction
end

function T.jobs_per_machine()
  local j = run([[insert into event(ts,agent,kind,path,data) values(1,'a','job-start','1','{"machine":"laptop"}'),(2,'a','job-end','1','{"exit":1,"s":120,"sync_s":0.5,"back_s":0.25}'),
 (3,'a','job-start','2','{"machine":"laptop"}'),(4,'a','job-end','2','{"exit":"lost","s":60}'),(5,'b','job-start','3','{"machine":null}');]],
    { env = NOGIT }).jobs
  local l = j.laptop
  eq({ l.jobs, l.minutes, l.exits["1"], l.lost, l.unfinished, l.sync_s, l.back_s }, { 2, 3.0, 1, 1, 0, 0.5, 0.25 })
  assert(j.here.unfinished == 1)
end

local function agent_transcripts(files)
  local h = tmp(); local d = h .. "/.claude/projects/-w"
  sh("mkdir -p " .. d)
  for f, body in pairs(files) do local fh = assert(io.open(d .. "/" .. f .. ".jsonl", "w")); fh:write(body); fh:close() end
  return run("insert into agent(name,cwd,started,status) values('jl-1','/w',1,'idle');", { home = h, env = NOGIT }).agents[1]
end

function T.transcript_name_is_exact()
  local rec = function(n) return '{"type":"agent-name","agentName":"' .. n .. '"}\n' end
  local a = agent_transcripts({ a = rec("jl-1"), b = rec("jl-11"), c = rec("jl-1-2"), d = rec("jl-10") })
  local names = {}
  for i, x in ipairs(a.transcripts) do names[i] = x:match("[^/]*$") end
  table.sort(names)
  eq(names, { "a.jsonl", "c.jsonl" })
end

function T.hook_bytes_by_source_and_brief_size()
  local h = function(c) return json.encode({ attachment = { type = "hook_additional_context", content = { c } } }) .. "\n" end
  local body = '{"type":"agent-name","agentName":"jl-1"}\n' .. '{"type":"user","message":{"content":"abcde"}}\n'
    .. h("swarm messages (x") .. h("machine: 1G") .. h("zzz") .. '{"attachment":{"type":"date"}}\n'
  local a = agent_transcripts({ a = body })
  eq(a.hook_bytes, { inbox = 17, machine = 11, other = 3 }); assert(a.brief_bytes == 5)
end

function T.cold_wakes()
  local function cw(...)
    local vals = {}
    for i, p in ipairs({ ... }) do vals[i] = ("(%d,'a','%s')"):format(p[1], p[2]) end
    return run("insert into event(ts,agent,kind) values" .. table.concat(vals, ","), { env = NOGIT }).always_loaded.cold_wakes
  end
  assert(cw({ 0, "push" }, { 4000, "wake" }, { 4100, "wake" }) == 1)  -- second wake is warm
  assert(cw({ 0, "push" }, { 1000, "compact" }, { 1100, "push" }, { 5000, "wake" }) == 1)
  assert(cw({ 0, "push" }, { 3000, "compact" }, { 3100, "wake" }) == 0)
end

function T.resources()
  local p = run([[insert into event(ts,agent,kind,data) values(10,null,'heavy-count','2'),(20,null,'pressure',null),(80,null,'pressure-end',null),
 (90,null,'pressure',null),(95,null,'heavy-count','1'),(30,'a','heavy-start','cabal build'),(40,'a','heavy-start','x'),(50,'b','orphan-kill','1 ghc');]],
    { env = NOGIT }).pressure
  eq({ p.episodes, p.total_s, p.ongoing, p.max_concurrent_heavy, p.orphan_kills }, { 2, 60, true, 2, 1 })
  eq(p.heavy_starts, { a = 2 })
end

function T.agent_line_anywhere_in_body()
  local d = tmp()
  local g = "git -C " .. d .. " -c user.name=x -c user.email=x@x "
  sh(g .. "init -q -b main && echo 1 > " .. d .. "/f && " .. g .. "add f && " .. g
    .. "commit -qm 't\n\n@@ -1 +1 @@\n\nSwarm-Agent: sp-a\n\nCo-authored-by: y' && " .. g .. "commit -q --allow-empty -m plain && "
    .. g .. "update-ref refs/remotes/origin/main HEAD")
  local r = run(nil, { cwd = d })
  assert(#r.commits_per_hour == 1 and r.commits_per_hour[1].agent == "sp-a" and r.not_swarm_commits == 1)
end

function T.text_report()
  local d = tmp()
  local env = { SWARM_DB = d .. "/swarm.db", SWARM_NAME = "t", HOME = d, GIT_DIR = "/nonexistent" }
  assert(select(3, proc.exec({ SWARM, "task", "add", "x" }, { env = env })) == 0)
  local out, err, code = proc.exec({ REPORT }, { env = env })
  assert(code == 0, err); assert(out:find("## tasks", 1, true))
end

local names = {}
for k in pairs(T) do names[#names + 1] = k end
table.sort(names)
local failed = 0
for _, k in ipairs(names) do
  local ok, err = xpcall(T[k], debug.traceback)
  if ok then print("ok    " .. k) else failed = failed + 1; print("FAIL  " .. k .. "\n" .. tostring(err)) end
end
print(("%d tests, %d failed"):format(#names, failed))
os.exit(failed == 0 and 0 or 1)
