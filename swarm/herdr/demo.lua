-- A made-up swarm for shot.sh: luajit swarm/herdr/demo.lua DIR [away|back|dead|stale], then swarm/herdr/shot.sh --fixture DIR out.png.
-- Writes DIR/swarm.db (a board mid-work: the limits reached, auto-spawn holding, a hung stayer, a blocked task),
-- DIR/proc (the machine reading and `ps` output), DIR/bin/ps and DIR/state (a cmd-cost history for repo "demo").
local here = debug.getinfo(1, "S").source:sub(2):match("^(.*)/[^/]*$") or "."
package.path = here .. "/../lua/?.lua;" .. package.path
local dir = assert(arg[1], "usage: luajit demo.lua DIR [away|back|dead|stale]...")
local want = {}  -- variants: the user away, just back (the digest card), watchd dead or older than the code
for i = 2, #arg do want[arg[i]] = true end
local stdlib = require "posix.stdlib"
os.execute(("mkdir -p '%s/proc/pressure' '%s/bin' '%s/state'"):format(dir, dir, dir))
stdlib.setenv("SWARM_DB", dir .. "/swarm.db")
stdlib.setenv("XDG_STATE_HOME", dir .. "/state")
os.remove(dir .. "/swarm.db")
os.remove(dir .. "/state/cmd-cost/history.db")
local db, cost, json = require "swarm.db", require "swarm.cost", require "swarm.json"
local c, now = db.connect(), os.time()
local function m(min) return now - math.floor(min * 60) end  -- minutes ago

local function put(path, s) local f = assert(io.open(path, "w")); f:write(s); f:close() end

-- agents: name, model, status, idle minutes, ctx, role, stay, claude pid, started (min ago), ended (min ago), files
for _, a in ipairs({
  { "ox-comms", "opus", "idle", 2, 141000, "communicator", "the user's channel", 100, 190 },
  { "ox-1", "opus", "working", 0, 236000, "implementer", nil, 110, 170, nil, { "engine/src/plan.rs", "engine/src/plan/cost.rs", "engine/tests/plan.rs" } },
  { "ox-2", "opus", "idle", 58, 391000, "reviewer", "PR reviews", 120, 165 },
  { "ox-3", "sonnet", "idle", 6, 88000, "implementer", nil, 130, 95, nil, { "migrations/0042_tenants.sql" } },
  { "ox-4", "sonnet", "idle", 21, 64000, "CI watcher", "main's CI", 140, 80 },
  { "ox-5", "sonnet", "working", 0, 31000, nil, nil, 150, 9, nil, { "docs/plan-cache.md" } },
  { "ox-6", "sonnet", "idle", 70, 362000, nil, nil, nil, 160, 70 },
  { "ox-7", "opus", "idle", 100, 204000, nil, nil, nil, 180, 100 },
}) do
  c:exec("insert into agent(name,model,status,last_active,ctx_tokens,role,stay,claude_pid,started,ended,snap,wt) values(?,?,?,?,?,?,?,?,?,?,?,?)",
    a[1], a[2], a[3], m(a[4]), a[5], a[6], a[7], a[8], m(a[9]), a[10] and m(a[10]), json.encode({ files = a[11] or {} }),
    a[1] ~= "ox-comms" and not a[10] and "/work/atlas-" .. a[1] or nil)
end
c:exec("update agent set hc='t1' where name='ox-comms'")  -- shot.sh's one terminal: the header's Communicator link shows
for k, v in pairs({ comms = "ox-comms", agent_min = "5", agent_max = "5",
  spawn_held = "auto-spawn holding: 5 live, the auto-spawn number is 5; 2 task(s) startable; max 5" }) do
  c:exec("insert into meta(k,v) values(?,?)", k, v)
end

-- tasks: title, state, owner, by, evidence, deps, question, lease minutes left
for _, k in ipairs({
  { "Planner: carry row estimates through joins", "done", "ox-7", "ox-comms", "PR #31 merged 4f2a9c1e" },
  { "Plan cache: key on the normalized query", "done", "ox-6", "ox-comms", "PR #33 merged 9be01d77" },
  { "Flaky test: plan_cache_evicts under load", "done", "ox-1", "ox-2", "PR #34 merged 1c3d5e7f, 40 runs green" },
  { "Planner: cost model for index scans", "claimed", "ox-1", "ox-comms", nil, nil, nil, 96 },
  { "Tenants: migration and backfill", "blocked", "ox-3", "ox-comms", nil, nil, "Backfill in one transaction, or in batches of 10k?", 110 },
  { "Docs: how the plan cache is keyed", "claimed", "ox-5", "ox-1", nil, nil, nil, 112 },
  { "Planner: cost model for hash joins", "open", nil, "ox-1" },
  { "Bench: plan time on the 200-table schema", "open", nil, "ox-2" },
  { "Tenants: per-tenant plan cache", "open", nil, "ox-comms", nil, "5" },
  { "Old: rewrite the parser", "dropped", nil, "ox-comms" },
}) do
  c:exec("insert into task(title,state,owner,created_by,evidence,deps,question,lease_until,model) values(?,?,?,?,?,?,?,?,?)",
    k[1], k[2], k[3], k[4], k[5], k[6], k[7], k[8] and now + k[8] * 60, "sonnet")
end

c:exec("update task set priority=0 where title like 'Planner: cost model for hash%'")  -- the shots show the priority chips
c:exec("update task set priority=3 where title like 'Bench:%'")
c:exec("update task set priority=1 where title like 'Docs:%'")

-- events, oldest first: minutes ago, agent, kind, path, data
for _, e in ipairs({
  { 170, "ox-comms", "spawn", nil, "ox-1" }, { 165, "ox-comms", "spawn", nil, "ox-2" },
  { 164, "ox-2", "role", nil, "reviewer" }, { 163, "ox-2", "stay", nil, "PR reviews" },
  { 100, "ox-7", "done", nil, "#1 PR #31 merged 4f2a9c1e" }, { 100, "ox-7", "end", nil, "landed" },
  { 95, "swarm", "spawn", nil, "auto #5" }, { 94, "ox-3", "claim", nil, "#5" },
  { 80, "ox-comms", "spawn", nil, "ox-4" }, { 79, "ox-4", "stay", nil, "main's CI" },
  { 71, "ox-6", "done", nil, "#2 PR #33 merged 9be01d77" }, { 70, "ox-6", "end", nil, "landed" },
  { 52, "ox-1", "done", nil, "#3 PR #34 merged 1c3d5e7f, 40 runs green" },
  { 50, "ox-1", "claim", nil, "#4" }, { 44, "ox-1", "task-add", nil, "#7" }, { 44, "ox-1", "task-add", nil, "#6" },
  { 38, nil, "pressure", nil, "machine: 3.9/31.3G mem available, pressure10 mem 14.2% cpu 61%" }, { 31, nil, "pressure-end" },
  { 30, "ox-comms", "limits", nil, "min 5 max 5" },
  { 24, "ox-2", "task-add", nil, "#8" },
  { 20, "ox-4", "stay-nowaiter" },
  { 12, "ox-1", "push", json.encode({ branch = "ox-1/index-scan-cost", subject = "planner: cost index scans by selectivity" }), "git push" },
  { 9, "swarm", "spawn", nil, "auto #6" }, { 9, "ox-5", "claim", nil, "#6" },
  { 8, "ox-2", "stay-check" },
  { 7, "ox-1", "spawn-refused", nil, "ox-8" },
  { 6, "ox-3", "block", nil, "#5 Backfill in one transaction, or in batches of 10k?" },
  { 5, "swarm", "spawn-held", nil, "auto-spawn holding: 5 live, the auto-spawn number is 5; 2 task(s) startable; max 5" },
  { 3, "ox-2", "stay-hung" },
}) do
  c:exec("insert into event(ts,agent,kind,path,data) values(?,?,?,?,?)", m(e[1]), e[2], e[3], e[4], e[5])
end
for _, x in ipairs({
  { 12, "ox-1", "ox-2", "PR #36 is ready: index scan costs. https://github.com/example/atlas/pull/36", 0, "dm" },
  { 6, "swarm", "ox-comms", "ox-3 is blocked on #5: Backfill in one transaction, or in batches of 10k?", 0, "system" },
  { 3, "swarm", "ox-comms", "ox-2 stays for 'PR reviews' and did not answer the liveness check (terminal t12, hc status idle). Unstick it with `hc send`, or end it.", 1, "system" },
}) do
  c:exec("insert into msg(ts,frm,dest,body,urgent,kind) values(?,?,?,?,?,?)", m(x[1]), x[2], x[3], x[4], x[5], x[6])
end
-- main's CI as watchd polled it (newest red), and watchd's own record: pid 1 stands for a live one (shot.sh makes it
-- its own pid), 2147483646 for a dead one; "stale": started before the swarm code last changed
local function isot(min) return os.date("!%Y-%m-%dT%H:%M:%SZ", m(min)) end
for i, r in ipairs({ { 9100412, 14, "failure", "5d02e6ab" }, { 9100377, 52, "success", "1c3d5e7f" }, { 9100301, 71, "success", "9be01d77" },
    { 9100266, 100, "success", "4f2a9c1e" } }) do
  c:exec("insert into ci(id,sha,status,conclusion,url,created,updated) values(?,?,'completed',?,?,?,?)", r[1], r[4], r[3],
    "https://github.com/example/atlas/actions/runs/" .. r[1], isot(r[2]), isot(r[2] - 6))
end
c:exec("insert into meta(k,v) values('watchd',?)", (want.dead and "2147483646" or "1") .. " t3")
c:exec("insert into meta(k,v) values('watchd_run',?)", json.encode({ cwd = "/tmp", started = m(want.stale and 190 or 0), flags = { "--comms", "ox-comms", "--auto-spawn" } }))
if want.back or want.away then  -- the user left an hour ago; "back": and returned just now
  c:exec("insert into meta(k,v) values('away',?)", m(60) .. " lunch")
  c:exec("update task set done_at=?, merged_at=?, pr=34 where id=3", m(52), m(51))
  if want.back then
    stdlib.setenv("SWARM_NAME", "human")
    require("swarm.agents").cmd_away(c, { back = true, note = {} })
  end
end
c:exec("insert into lock(path,agent,reason,since) values('migrations/0042*','ox-3','tenants migration',?)", m(90))

-- the machine: memory nearly short, and who holds it (pid ppid rss_kb etime time args)
put(dir .. "/proc/meminfo", "MemTotal: 32823000 kB\nMemAvailable: 6100000 kB\n")
put(dir .. "/proc/pressure/memory", "some avg10=4.20 avg60=0 avg300=0 total=0\n")
put(dir .. "/proc/pressure/cpu", "some avg10=38.50 avg60=0 avg300=0 total=0\n")
put(dir .. "/proc/ps", table.concat({
  "100 1 610000 190:00 2:10 claude", "110 1 720000 170:00 9:40 claude", "120 1 690000 165:00 7:02 claude",
  "130 1 540000 95:00 3:31 claude", "140 1 480000 80:00 1:12 claude", "150 1 450000 9:00 0:40 claude",
  "111 110 9437184 6:12 21:05 cargo test --release -p planner", "112 110 1258291 6:12 2:00 rustc --crate-name planner",
  "151 150 310000 1:05 0:12 node /x/bin/mdbook build", "131 130 2202009 41:00 0:30 postgres -D /tmp/tenants",
  "900 1 800000 300:00 4:00 claude", "901 900 3355443 12:30 8:15 node /x/bin/vite build",
}, "\n") .. "\n")
put(dir .. "/bin/ps", '#!/bin/sh\nexec cat "$SWARM_PROC/ps"\n')
os.execute(("chmod +x '%s/bin/ps'"):format(dir))

-- the cmd-cost history of repo "demo" (shot.sh's demo repo): agent, command, wall s, cpu s, peak kb, minutes ago
local h = cost.open()
for _, r in ipairs({
  { "ox-7", "cargo test --release -p planner", 410, 1880, 11744051, 150 },
  { "ox-1", "cargo test --release -p planner", 372, 1790, 9856614, 61 },
  { "ox-6", "cargo build --release", 245, 1310, 7130316, 120 },
  { "ox-1", "cargo bench --bench plan_time", 905, 2400, 5033164, 75 },
  { "ox-3", "psql -f migrations/0042_tenants.sql", 188, 40, 2306867, 33 },
  { "ox-1", "cargo clippy --all-targets", 96, 420, 3460300, 14 },
}) do
  cost.record(h, { ts = m(r[6]), repo = "demo", agent = r[1], cmd = r[2], wall_s = r[3], cpu_s = r[4], peak_kb = r[5] })
end
print(dir)
