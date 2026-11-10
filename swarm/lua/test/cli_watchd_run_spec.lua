-- CLI tests ported from test_swarm.py (fake_proc .. test_run_remote_job_telemetry): one watchd, machine note,
-- memory pressure, CI red tasks, swarm run. Harness: cli.lua.
local json, util = require "swarm.json", require "swarm.util"
local cjson = require "cjson"
local unistd = require "posix.unistd"
local T = {}

local OLD = os.time() - 3600
local function put(path, text) local f = assert(io.open(path, "w")); f:write(text); f:close() end
local function read(...) return assert(util.slurp(table.concat({ ... }, "/"))) end
local function mkdir(p) os.execute("mkdir -p " .. util.shquote(p)) end
local function exists(p) return util.slurp(p) ~= nil or os.execute("test -e " .. util.shquote(p)) == 0 end
local function sh(cmd) local p = io.popen(cmd); local s = p:read("*a"); p:close(); return s end

local function fake_proc(t, avail_kb, psi)
  local r = t.d .. "/proc"
  mkdir(r .. "/pressure")
  put(r .. "/uptime", "10000.0 0\n")
  put(r .. "/meminfo", ("MemTotal: 32000000 kB\nMemAvailable: %d kB\n"):format(avail_kb or 20000000))
  for _, k in ipairs { "memory", "cpu" } do
    put(r .. "/pressure/" .. k, ("some avg10=%s avg60=0 avg300=0 total=0\n"):format(psi or "1.0"))
  end
  t:fake("ps", '#!/bin/sh\ncat "$SWARM_PROC"/[0-9]*/ps 2>/dev/null; exit 0\n')  -- machine.procs() reads the fixture
  return r
end

local tck
local function add_proc(r, pid, ppid, comm, argv, o)
  o = o or {}
  tck = tck or tonumber(sh("getconf CLK_TCK"))
  local d = r .. "/" .. pid
  mkdir(d)
  local f = { "S", tostring(ppid) }
  for _ = 1, 17 do f[#f + 1] = "0" end
  f[#f + 1] = ("%d"):format((10000 - (o.age_s or 240)) * tck)
  f[#f + 1] = "0"
  f[#f + 1] = ("%d"):format(o.rss_pages or 0)
  put(d .. "/stat", ("%d (%s) %s"):format(pid, comm, table.concat(f, " ")))
  put(d .. "/cmdline", table.concat(argv, "\0") .. "\0")
  put(d .. "/oom_score_adj", "0")
  put(d .. "/ps", ("%d %d %d %d:%02d 0:00 %s\n"):format(pid, ppid, (o.rss_pages or 0) * 4, math.floor((o.age_s or 240) / 60), (o.age_s or 240) % 60, table.concat(argv, " ")))
  if o.cwd then assert(unistd.link(o.cwd, d .. "/cwd", true)) end
end

local function swp(t, who, proc, ...)
  local args = { ... }
  local o = type(args[#args]) == "table" and table.remove(args) or {}
  o.env = o.env or {}
  o.env.SWARM_PROC = proc
  args[#args + 1] = o
  return t:sw(who, unpack(args))
end

local function hookp(t, who, proc, cmd)
  local r = swp(t, who, proc, "hook", "pre-tool",
    { stdin = json.encode({ cwd = t.cwd[who], tool_name = "Bash", tool_input = { command = cmd } }) })
  if util.strip(r.stdout) == "" then return {} end
  return json.decode(r.stdout).hookSpecificOutput
end

local function comms_tick(t) t:sw("a", "watchd", "--once", "--comms", "comms", "--max-agents", "0") end
local function idle(t, name, kw)
  kw = kw or {}
  kw.status, kw.last_active = "idle", OLD
  t:agent(name, kw)
end
local function ended(t, name) return t:q1("select ended e from agent where name=?", name).e ~= nil end
local function rev(t) return util.strip(t:git(t.repo, "rev-parse", "HEAD")) end
local function lines(s) return #util.splitlines(s) end

function T.test_one_watchd(t)
  t:sw("a", "join")
  t:q("insert or replace into meta(k,v) values('watchd',?)", unistd.getpid() .. " T1")  -- a live pid
  local r = t:sw("a", "watchd", "--once", { ok = false })
  t:has(r.stderr, "already runs"); t:has(r.stderr, "T1")
  t:sw("a", "watchd", "--once", "--takeover")
  t:hasnt(t:q1("select v from meta where k='watchd'").v, "T1")
end

function T.test_machine_note_and_patterns(t)
  local pr = fake_proc(t)
  t:hook("a", "session"); t:hook("b", "session")
  t:q("update agent set claude_pid=100 where name='a'")
  add_proc(pr, 100, 1, "claude", { "claude" })
  add_proc(pr, 101, 100, "bash", { "bash", "-c", "x" })
  add_proc(pr, 102, 101, "cabal", { "/nix/store/x/bin/cabal", "build" }, { rss_pages = 1000000 / 4 })
  add_proc(pr, 200, 1, "node", { "node", "/x/bin/tsc", "-b" }, { rss_pages = 500000 / 4 })  -- not a swarm agent's
  add_proc(pr, 103, 101, "ghc-9.10.3", { "/s/ghc-9.10.3", "--make" }, { rss_pages = 2000000 / 4 })
  hookp(t, "b", pr, "nix develop -c env TPG_SOCK=/m/.dev/.s.PGSQL.5432 cabal build")  -- b starts one: logged
  local o = hookp(t, "a", pr, "nix develop -c env TPG_SOCK=/m/.dev/.s.PGSQL.5432 cabal build")
  assert(o.permissionDecision == nil)
  local n = o.additionalContext
  assert(lines(n) <= 6, n)
  t:has(n, "machine: 19.1/30.5G")
  assert(n:find("running: ghc%-9%.10%.3 %-%-make .*%(a%)"), n)
  t:has(n, "running: tsc -b"); t:has(n, "(other session)")
  t:has(n, "started in the last 60s: b:")
  t:eq(hookp(t, "a", pr, "git commit -m 'make it'"), {})
  t:eq(hookp(t, "a", pr, "nix run .#dev"), {})
  for _, c in ipairs { "nix build .#server", "nix flake check", "spago build", "purs compile", "npx playwright test" } do
    t:has(hookp(t, "a", pr, c).additionalContext, "machine:", c)
  end
  mkdir(t.repo .. "/.claude")
  put(t.repo .. "/.claude/swarm.json", '{"heavy": ["\\\\bfoo-build\\\\b"]}')
  t:has(hookp(t, "a", pr, "foo-build all").additionalContext, "machine:")
end

function T.test_pressure_edge_oom_and_orphans(t)
  local pr = fake_proc(t, 2000000)  -- 6% available: high
  t:hook("a", "session"); t:hook("b", "session")
  t:q("update agent set claude_pid=100 where name='a'")
  add_proc(pr, 100, 1, "claude", { "claude" })
  add_proc(pr, 102, 100, "cabal", { "cabal", "build" }, { rss_pages = 1000000 / 4 })
  -- b is ended; its worktree holds a build reparented to init
  t:q("update agent set ended=1 where name='b'")
  add_proc(pr, 300, 1, "ghc-9.10.3", { "ghc-9.10.3", "--make" }, { rss_pages = 3000000 / 4, cwd = t.wt })
  swp(t, "a", pr, "watchd", "--once")
  local ev = {}
  for _, r in ipairs(t:q("select kind from event where kind in ('pressure','pressure-end','orphan-kill') order by id")) do
    ev[#ev + 1] = r.kind
  end
  t:eq(ev, { "pressure", "orphan-kill" })
  local notes = t:q("select dest,body from msg where kind='notice'")
  t:eq(#notes, 1); t:eq(notes[1].dest, "a"); t:has(notes[1].body, "ghc-9.10.3")
  t:eq(read(pr, "102", "oom_score_adj"), "500")
  t:eq(read(pr, "300", "oom_score_adj"), "0")  -- not an agent's: left alone
  -- still high: no second notice (edge-triggered); leaves high: pressure-end
  swp(t, "a", pr, "watchd", "--once")
  t:eq(t:q1("select count(*) n from event where kind='pressure'").n, 1)
  fake_proc(t, 20000000)
  swp(t, "a", pr, "watchd", "--once")
  t:eq(t:q1("select count(*) n from event where kind='pressure-end'").n, 1)
end

function T.test_machine_line_at_decisions(t)
  local pr = fake_proc(t)
  t:hook("a", "session")
  t:sw("a", "task", "add", "x"); t:sw("a", "task", "add", "y")
  t:has(swp(t, "a", pr, "board").stdout, "machine: 19.1/30.5G")
  local c = swp(t, "a", pr, "task", "claim", "1").stdout
  t:has(c, "machine: 19.1/30.5G"); t:hasnt(c, "started in the last")
  fake_proc(t, 2000000)  -- high pressure: the full note
  add_proc(pr, 100, 1, "claude", { "claude" })
  t:has(swp(t, "a", pr, "task", "claim", "2").stdout, "machine: 1.9/30.5G")
end

function T.test_pressure_notice_reaches_stayers(t)
  local pr = fake_proc(t, 2000000)
  t:hook("a", "session"); t:hook("s", "session")
  t:q("update agent set stay='review' where name='s'")
  swp(t, "a", pr, "watchd", "--once")
  t:eq(t:q1("select count(*) n from msg where kind='notice' and dest='s'").n, 1)
end

function T.test_ci_red_is_one_task_closed_on_green(t)
  local function commit(who) t:git(t.repo, "commit", "-q", "--allow-empty", "-m", "x\n\nSwarm-Agent: " .. who) end
  local green = rev(t)
  commit("a"); commit("gone")
  local red = rev(t)
  local runs = {
    { databaseId = 9, headSha = red, conclusion = "failure", status = "completed", url = "http://ci/9",
      createdAt = "2026-11-08T10:05:00Z", updatedAt = "2026-11-08T10:08:00Z", event = "push" },
    { databaseId = 8, headSha = green, conclusion = "success", status = "completed", url = "http://ci/8",
      createdAt = "2026-11-08T10:00:00Z", updatedAt = "2026-11-08T10:03:00Z", event = "push" } }
  local function gh(rs)
    t:fake("gh", ("#!/bin/sh\n[ \"$1\" = api ] && echo '%s' || echo 'step Build failed'\n"):format(cjson.encode(rs)))
  end
  gh(runs)
  t:agent("a"); t:agent("gone", { ended = 1 }); t:agent("comms")
  local function go() t:sw("a", "watchd", "--once", "--ci", "--comms", "comms", { cwd = t.repo }) end
  local function reset() t:q("delete from meta where k like 'ci%'") end
  t:sw("a", "task", "add", "earlier work")
  go(); go()  -- second tick: edge-triggered
  local m = t:q("select dest,body from msg where kind='system' order by id")
  t:eq(#m, 1); t:eq(m[1].dest, "a")
  t:has(m[1].body, "http://ci/9"); t:has(m[1].body, "swarm task claim 2")
  local red_tasks = t:q("select id,body,state from task where title like 'main red:%'")
  t:eq(#red_tasks, 1); t:has(red_tasks[1].body, "Build failed")
  local board = t:sw("a", "board").stdout
  assert(board:find("main red", 1, true) < board:find("earlier work", 1, true))  -- the red task starts first
  -- a later red in the same stretch is the same task
  local later = {}
  for k, v in pairs(runs[1]) do later[k] = v end
  later.databaseId, later.createdAt = 10, "2026-11-08T10:10:00Z"
  table.insert(runs, 1, later)
  gh(runs); reset(); go()
  t:eq(#t:q("select 1 x from task where title like 'main red:%'"), 1)
  t:eq(#t:q("select 1 x from msg where kind='system'"), 1)
  t:has(t:q1("select body from task where id=2").body, "Later red: run 10")
  -- the fixer's done keeps its claim; a re-run of the reds leaves an older green on top: still open
  t:sw("a", "task", "claim", "2")
  t:has(t:sw("a", "task", "done", "2", "--evidence", "abc").stdout, "stays yours")
  t:eq(t:q1("select state from task where id=2").state, "claimed")
  local rerun = {}
  for i, r in ipairs(runs) do
    rerun[i] = r
    if r.conclusion == "failure" then
      rerun[i] = {}
      for k, v in pairs(r) do rerun[i][k] = v end
      rerun[i].status, rerun[i].conclusion = "in_progress", cjson.null
    end
  end
  gh(rerun); reset(); go()
  t:eq(t:q1("select state from task where id=2").state, "claimed")
  -- green closes it, and tells its owner
  local g = {}
  for k, v in pairs(runs[1]) do g[k] = v end
  g.databaseId, g.conclusion, g.createdAt = 11, "success", "2026-11-08T10:20:00Z"
  table.insert(runs, 1, g)
  gh(runs); reset(); go()
  local d = t:q1("select state,evidence from task where id=2")
  t:eq({ d.state, d.evidence }, { "done", "green run 11 at " .. red:sub(1, 7) })
  t:has(t:q1("select body from msg where dest='a' order by id desc limit 1").body, "is done; stop fixing it")
  -- no live suspect: a new task, and comms hears of it
  t:q("update agent set ended=1 where name='a'"); t:q("delete from event where kind='ci-red'")
  table.remove(runs, 1)
  gh(runs); reset(); t:q("delete from ci")
  go()
  local dests = {}
  for _, r in ipairs(t:q("select dest from msg where kind='system' order by id")) do dests[#dests + 1] = r.dest end
  t:eq(dests, { "a", "a", "comms" })
  t:eq(#t:q("select 1 x from task where title like 'main red:%' and state='open'"), 1)
end

-- ---- swarm run ----
-- Fake hc and ssh: the 'laptop' is a home dir here; rsync is real. Per-terminal `hc get` answers come from <d>/get.<terminal>.
local function fake_remote(t, state)
  t.home = t.d .. "/laptop-home"; mkdir(t.home)
  t.hclog = t.d .. "/hc.log"
  local H, D = util.shquote(t.home), util.shquote(t.d)
  local m = json.encode({ machines = { { name = "laptop", state = state or "connected", target = "u@laptop" } } })
  t:fake("hc", ([[#!/bin/sh
echo "$*" >> %s/hc.log
case "$1 $2" in "machine ls") echo '%s'; exit 0;; esac
case "$1" in
  ls) echo '{"terminals": []}';;
  run) while [ "$1" != sh ]; do shift; done
    (cd %s && HOME=%s "$@" >/dev/null); echo $? > %s/rc; echo '{"address": "laptop/t1"}';;
  wait) [ -e %s/lost ] && exit 3
    echo "{\"ended\": true, \"exit_code\": $(cat %s/rc)}";;
  get) if [ -f %s/get.$2 ]; then cat %s/get.$2; else echo '{"error": {"kind": "not_found", "message": "no terminal"}}'; exit 3; fi;;
  exec) while [ "$1" != --timeout ]; do shift; done; shift 2; cd %s && HOME=%s "$@" 2>/dev/null;;
esac
]]):format(D, m, H, H, D, D, D, D, D, H, H))
  t:fake("ssh", ([[#!/bin/sh
while [ "$1" = -o ] || [ "$1" = -l ]; do shift 2; done
shift; cd %s && HOME=%s exec sh -c "$*"
]]):format(H, H))
end

function T.test_run_remote_syncs_runs_and_brings_back(t)
  fake_remote(t)
  mkdir(t.wt .. "/.claude")
  put(t.wt .. "/.claude/swarm.json", json.encode({ run = {
    prefix = "env", env = { "^APP_" }, set = { T = "{dir}/target" }, bring_back = { "out/" } } }))
  t:write("b", ".gitignore", "out/\nsecret.txt\n"); t:write("b", "secret.txt", "s")
  t:sw("b", "task", "add", "t"); t:sw("b", "task", "claim", "1")
  local cmd = ('echo "app=$APP_Y k=$K t=$T"; echo new > new.txt; echo job > a.txt; mkdir -p out; echo r > out/r.txt; '
    .. 'echo mine > %s/b.txt; echo theirs > b.txt; exit 3'):format(t.wt)
  local r = t:sw("b", "run", "--on", "laptop", "--env", "K=1", "--", cmd, { ok = false, env = { APP_Y = "2" } })
  t:eq(r.code, 3, r.stderr)
  local src = t.home .. "/.cache/swarm-run/repo/wt/src"
  t:has(r.stdout, "app=2 k=1 t=" .. t.home .. "/.cache/swarm-run/repo/wt/target")
  assert(r.stdout:find("job j1 exit 3 on laptop, 0m%d%ds %(sync [%d.]+s, back [%d.]+s%), tree %x%x%x%x%x%x%x; log: "), r.stdout)
  assert(not exists(src .. "/secret.txt"))  -- ignored files stay here
  t:eq({ read(t.wt, "new.txt"), read(t.wt, "a.txt"), read(t.wt, "out/r.txt") }, { "new\n", "job\n", "r\n" })
  t:eq(read(t.wt, "b.txt"), "mine\n")  -- edited here during the job: kept, theirs beside the log
  t:eq(read(t.d, "jobs", "1", "kept", "b.txt"), "theirs\n")
  t:has(r.stdout, "b.txt are in")
  local ev = {}
  for _, row in ipairs(t:q("select kind,data from event where kind like 'job-%'")) do ev[row.kind] = json.decode(row.data) end
  t:eq({ ev["job-start"].machine, ev["job-start"].task, ev["job-start"].hc }, { "laptop", 1, "laptop/t1" })
  t:eq({ ev["job-end"].exit, #ev["job-end"].tree }, { 3, 40 })
  local hc = read(t.hclog)
  t:has(hc, "--label swarm-agent=b --label swarm-job=1 --label swarm-wt=repo/wt --label swarm-task=1")
  t:has(hc, "rm laptop/t1")
  for _, j in ipairs(json.decode(t:sw("b", "state", "--json").stdout).running) do assert(j.machine == nil) end
end

function T.test_run_never_ran_or_lost_is_255(t)
  fake_remote(t, "disconnected")
  local r = t:sw("b", "run", "--on", "laptop", "--", "true", { ok = false })
  t:eq(r.code, 255)
  t:has(r.stderr, "laptop is disconnected; the job never ran")
  t:eq(t:q1("select count(*) n from event where kind like 'job-%'").n, 0)
  fake_remote(t)
  put(t.d .. "/lost", "")
  r = t:sw("b", "run", "--on", "laptop", "--", "true", { ok = false })
  t:eq(r.code, 255)
  t:has(r.stdout, "lost on laptop"); t:has(r.stdout, "hc wait laptop/t1")
  t:eq(json.decode(t:q1("select data from event where kind='job-end'").data).exit, "lost")
end

function T.test_run_local_records_job(t)
  local r = t:sw("b", "run", "--", "echo hi; exit 2", { ok = false })
  t:eq(r.code, 2)
  assert(r.stdout:find("^hi\njob j1 exit 2 on this machine, .*tree %x%x%x%x%x%x%x"), r.stdout)
  local ks = {}
  for _, row in ipairs(t:q("select kind from event where kind like 'job-%' order by id")) do ks[#ks + 1] = row.kind end
  t:eq(ks, { "job-start", "job-end" })
end

function T.test_run_note_state_and_cleanup(t)
  fake_remote(t)
  local pr = fake_proc(t)
  t:agent("a")
  local now = os.time()
  t:q("insert into meta values('machines',?)", json.encode({
    laptop = { state = "connected", ts = now, cores = 24, load = 3.5, avail_kb = 80 * 2 ^ 20, total_kb = 93 * 2 ^ 20, psi = 0.0 },
    nas = { state = "disconnected", ts = now, since = now - 600 } }))
  local d = ".cache/swarm-run/repo/wt"
  t:q("insert into event(ts,agent,kind,path,data) values(?,?,?,?,?)", now - 120, "a", "job-start", "1",
    json.encode({ machine = "laptop", hc = "laptop/t9", wt = util.strip(sh("realpath " .. util.shquote(t.wt))), dir = d,
      cmd = "cargo test -p x", pid = 999999999 }))
  local n = hookp(t, "a", pr, "swarm run --on laptop -- cargo test").additionalContext  -- swarm run is heavy
  t:has(n, "laptop: 80/93G available, load 3.5 on 24 cores, mem pressure 0%, jobs: a cargo test -p x 2m")
  t:has(n, "nas: disconnected since")
  local lost = {}
  for _, j in ipairs(json.decode(t:sw("a", "state", "--json").stdout).running) do
    if j.machine then lost[#lost + 1] = { j.machine, j.job, j.lost } end
  end
  t:eq(lost, { { "laptop", "1", true } })  -- swarm run gone, terminal gone
  -- watchd's probe of each machine, only from a Herdr terminal
  t:sw("a", "watchd", "--once", { hc = "t1", cwd = t.repo })
  local lap = json.decode(t:q1("select v from meta where k='machines'").v).laptop
  t:eq(lap.state, "connected"); assert(lap.cores > 0); assert(lap.total_kb > 0)
  -- a landed worktree's dirs go on every machine its jobs used
  mkdir(t.home .. "/" .. d .. "/src")
  idle(t, "e", { wt = t.wt })
  comms_tick(t)
  assert(ended(t, "e"))
  t:has(read(t.hclog), "exec --on laptop --timeout 120 rm -rf " .. d)
  assert(not exists(t.home .. "/" .. d))
end

function T.test_run_remote_job_telemetry(t)
  fake_remote(t)
  t:agent("a")
  local now = os.time()
  local tree = io.popen("echo $$; exec sh -c 'sleep 30 & sleep 30 & wait' >/dev/null")
  local pid = tonumber(tree:read("*l"))
  t:defer(function() os.execute(("pkill -P %d; kill %d"):format(pid, pid)) end)
  os.execute("sleep 0.3")
  put(t.d .. "/get.t9", json.encode({ state = "live", pid = pid }))
  put(t.d .. "/get.t7", json.encode({ state = "exited" }))
  t:q("insert into meta values('machines',?)", json.encode({ laptop = { state = "connected", ts = now, jobs = { ["2"] = { gone = now - 3601 } } } }))
  for _, j in ipairs { { "1", "laptop/t9", 60 }, { "2", "laptop/t8", 9000 }, { "3", "laptop/t7", 30 }, { "4", "nas/t1", 30 } } do
    t:q("insert into event(ts,agent,kind,path,data) values(?,?,?,?,?)", now - j[3], "a", "job-start", j[1],
      json.encode({ machine = j[2]:match("^[^/]+"), hc = j[2], cmd = "cargo test", pid = 999999999 }))
  end
  t:sw("a", "watchd", "--once", { hc = "t1", cwd = t.repo })
  t:has(read(t.hclog), "sh t7 t8 t9\n")  -- one exec carries the job terminals, named as the machine names them
  local ms = json.decode(t:q1("select v from meta where k='machines'").v)
  local js = ms.laptop.jobs
  assert(js["1"].rss_kb > 0)  -- sh and both sleeps
  t:eq(js["2"], { gone = now - 3601 }); t:eq(js["3"], { gone = js["3"].gone })
  local exits = {}
  for _, row in ipairs(t:q("select data from event where kind='job-end'")) do exits[#exits + 1] = json.decode(row.data).exit end
  t:eq(exits, { "lost" })  -- job 2: gone over an hour
  ms.nas = { state = "disconnected", ts = now, since = now }
  t:q("update meta set v=? where k='machines'", json.encode(ms))
  local run, ids = {}, {}
  for _, j in ipairs(json.decode(t:sw("a", "state", "--json").stdout).running) do
    if j.machine then run[j.job] = j; ids[#ids + 1] = j.job end
  end
  table.sort(ids)
  t:eq(ids, { "1", "3", "4" })
  t:eq({ run["1"].lost, run["1"].rss_kb, run["3"].lost, run["3"].rss_kb }, { false, js["1"].rss_kb, true, nil })
  t:eq({ run["4"].unreachable, run["4"].lost }, { true, false })
  t:has(t:sw("a", "machine").stdout, " cargo test 1m 0.0G")
end

return T
