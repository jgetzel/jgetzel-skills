-- CLI tests ported from test_swarm.py (test_auto_spawn_once_within_cap .. test_state_json_old_db): auto-spawn, spawn,
-- the cold-cache rule, waiters, `state --json`. Harness: cli.lua.
local json, util = require "swarm.json", require "swarm.util"
local sqlite3 = require "lsqlite3"
local unistd, wait, stdlib, fcntl = require "posix.unistd", require "posix.sys.wait", require "posix.stdlib", require "posix.fcntl"
local ptime = require "posix.time"
local cli = require "test.cli"
local T = {}

local function put(path, text, mode)
  local f = assert(io.open(path, "w")); f:write(text); f:close()
  if mode then os.execute("chmod " .. mode .. " " .. util.shquote(path)) end
end
local function sleep(s) ptime.nanosleep({ tv_sec = math.floor(s), tv_nsec = (s % 1) * 1e9 }) end
local function exists(p) local f = io.open(p); if f then f:close() end return f ~= nil end
local function touch(p) put(p, "") end
local function stj(t, ...) return json.decode(t:sw("a", "state", "--json", ...).stdout) end
local function names(xs) local r = {} for i, x in ipairs(xs) do r[i] = x.argv[1] end return r end

-- A background `swarm <args>` as who (no HC_TERMINAL_ID), stderr to a file; returns {pid=, errf=}.
local function bg(t, who, errname, ...)
  local errf = t.d .. "/" .. errname
  local args = { cli.SWARM, ... }
  local pid = unistd.fork()
  if pid == 0 then
    local fd = fcntl.open(errf, fcntl.O_WRONLY + fcntl.O_CREAT + fcntl.O_TRUNC, 420)
    unistd.dup2(fd, 2)
    stdlib.setenv("SWARM_DB", t.db); stdlib.setenv("SWARM_NAME", who); stdlib.setenv("HC_TERMINAL_ID", nil)
    unistd.execp(args[1], { select(2, unpack(args)) })
    unistd._exit(127)
  end
  t:defer(function() pcall(wait.wait, pid, wait.WNOHANG) end)
  return { pid = pid, errf = errf }
end
-- exit code of a background job, failing if it outlives secs
local function reap(w, secs)
  for _ = 1, secs * 5 do
    local p, how, code = wait.wait(w.pid, wait.WNOHANG)
    if p ~= 0 then return how == "exited" and code or -code end
    sleep(0.2)
  end
  error("still running after " .. secs .. "s")
end

-- ---- auto-spawn ----
local function tick(t, cap) t:sw("a", "watchd", "--once", "--comms", "t-comms", "--max-agents", tostring(cap), "--min-free-mem", "0") end
local function two_haiku(t) for _, n in ipairs({ "t-comms", "t-1" }) do t:agent(n, { status = "working", model = "haiku" }) end end
local function spawned(t)
  local r = {}
  for i, x in ipairs(t:launched()) do
    local m
    for j, a in ipairs(x.argv) do if a == "--model" then m = x.argv[j + 1] end end
    r[i] = { x.argv[1], m }
  end
  return r
end

function T.test_auto_spawn_once_within_cap(t)
  t:fakes(); two_haiku(t)
  t:sw("a", "task", "add", "do it")
  tick(t, 1)
  t:eq(spawned(t), {})  -- at the cap
  tick(t, 2)
  t:eq(spawned(t), { { "t-2", "haiku" } })
  t:eq(t:q1("select owner,state from task").owner, "t-2")
  assert(t:q1("select first_claimed_at f from task").f, "auto-spawn stamps the claim time")
  tick(t, 2)
  t:eq(#spawned(t), 1)  -- the task is claimed: no second spawn
end

function T.test_auto_spawn_failure_backs_off(t)
  t:fakes(); two_haiku(t)
  touch(t.d .. "/launch.fail")
  t:sw("a", "task", "add", "do it")
  tick(t, 2)
  tick(t, 2)  -- inside the backoff window: no second launch, no second notice
  t:eq(names(t:launched()), { "t-2" })
  local notes = {}
  for _, r in ipairs(t:q("select body from msg where dest='t-comms'")) do
    if r.body:find("auto-spawn", 1, true) then notes[#notes + 1] = r.body end
  end
  t:eq(#notes, 1)
  t:has(notes[1], "no Herdr window")
  t:q("update meta set v='0,300,t-2' where k='spawn_backoff'")  -- window over
  tick(t, 2)
  t:eq(names(t:launched()), { "t-2", "t-2" })  -- same name reused
  t:eq(t:q1("select count(*) n from msg where body like '%auto-spawn%'").n, 1)  -- still one notice
end

function T.test_auto_spawn_gives_up_after_k_failures(t)
  t:fakes(); two_haiku(t)
  touch(t.d .. "/launch.fail")
  t:sw("a", "task", "add", "do it")
  for _ = 1, 7 do
    tick(t, 2)
    t:q("update meta set v='0,300,t-2' where k='spawn_backoff'")  -- window over
  end
  t:eq(#t:launched(), 5)  -- K=5, then no more launches
  local urgent = t:q("select body from msg where dest='t-comms' and urgent=1 and body like '%in a row%'")
  t:eq(#urgent, 1)
  t:has(urgent[1].body, "no Herdr window")
end

-- ---- spawn ----
function T.test_spawn_task_claims_before_launch(t)
  t:fakes()
  t:sw("a", "task", "add", "do it")
  t:sw("a", "spawn", "t-9", "--model", "haiku", "--task", "1")
  t:eq(t:launched()[1].task, { { "t-9", "claimed" } })  -- claimed by the new name before launch ran
  t:eq(t:q1("select hc from agent where name='t-9'").hc, "hc1")
  t:has(t:sw("a", "spawn", "t-9", "--model", "haiku", "--task", "1", { ok = false }).stderr, "live agent")  -- a live name is refused
end

function T.test_spawned_agent_skips_older_broadcasts(t)
  t:fakes()
  t:sw("a", "task", "add", "do it")
  t:sw("a", "post", "@all", "old rule from another run")
  t:sw("a", "spawn", "t-9", "--model", "haiku", "--task", "1")
  t:sw("a", "post", "@all", "new rule")
  local out = t:sw("t-9", "read", { hc = "hc1" }).stdout
  t:hasnt(out, "old rule"); t:has(out, "new rule")
end

function T.test_spawn_launch_failure_keeps_live_agent(t)
  t:fakes(); t:set_hc({ name = "t-9", address = "t7" })
  touch(t.d .. "/launch.fail")
  t:sw("a", "task", "add", "do it")
  t:sw("a", "spawn", "t-9", "--model", "haiku", "--task", "1")
  local r = t:q1("select owner,state from task")
  t:eq({ r.owner, r.state }, { "t-9", "claimed" })
  t:eq(t:q1("select hc from agent where name='t-9'").hc, "t7")
end

function T.test_launch_sh_survives_failure_after_hc_run(t)
  local fb = t.d .. "/lfb"
  os.execute("mkdir " .. fb)
  local j = json.encode({ spaces = { { id = "s", tabs = { { id = "b", terminals = { { terminal = "t1" } } } } } } })
  put(fb .. "/hc", "#!/bin/sh\necho '{\"address\": \"t5\"}'\n", "755")
  put(fb .. "/herdr-app", "#!/bin/sh\n[ \"$1\" = ls ] && echo '" .. j .. "' || exit 1\n", "755")
  local sh = cli.SWARM:match("^(.*)/[^/]*$") .. "/../relaunch/launch.sh"
  local r = t:exec({ sh, "x", "tab", "task" }, { env = { PATH = fb .. ":" .. cli.PATH, HC_TERMINAL_ID = "t1" } })
  t:eq({ r.code, util.splitlines(util.strip(r.stdout))[#util.splitlines(util.strip(r.stdout))] }, { 0, "t5" }, r.stderr)
end

function T.test_spawn_task_launch_failure_rolls_back(t)
  t:fakes()
  touch(t.d .. "/launch.fail")
  t:sw("a", "task", "add", "do it")
  t:sw("a", "spawn", "t-9", "--model", "haiku", "--task", "1", { ok = false })
  local r = t:q1("select owner,state from task")
  t:eq({ r.owner, r.state }, { nil, "open" })
  assert(t:q1("select ended from agent where name='t-9'").ended)
end

function T.test_rules_appended_to_spawn(t)
  t:fakes()
  t:eq(util.strip(t:sw("a", "rules", "set", "never", "edit", "main").stdout), "never edit main")
  t:sw("a", "spawn", "t-9", "--model", "haiku", "--", "go")
  t:has(t:launched()[1].argv[3], "never edit main")
end

-- ---- cold-cache rule ----
local function sendmsg(t, to, text)
  return t:hook("a", "pre-tool", { tool_name = "SendMessage", tool_input = { to = to, message = text or "hi" } })
end
local function cache(extra)
  local c = { status = "idle", ctx_tokens = 140000, compacted_at = 0 }
  for k, v in pairs(extra) do c[k] = v end
  return c
end

function T.test_cold_cache_cheap_cases_and_cold(t)
  t:agent("a")
  local now = os.time()
  local cold = cache({ last_active = now - 72 * 60 })
  local function with(k, v) local c = cache({}); for a, b in pairs(cold) do c[a] = b end; c[k] = v; return c end
  local cheap = { working = with("status", "working"), warm = with("last_active", now - 10 * 60),
                  compacted = with("compacted_at", now - 60), small = with("ctx_tokens", 30000) }
  for n, kw in pairs(cheap) do
    t:agent(n, kw)
    t:eq(sendmsg(t, n), {}, n)
  end
  t:agent("cold", cold)
  local out = sendmsg(t, "cold")
  t:eq(out.permissionDecision, "deny")
  t:has(out.permissionDecisionReason, "idle 72 min")
  t:has(out.permissionDecisionReason, "140k")
  t:eq(t:q1("select path from event where kind='deny-cold'").path, "cold")
  t:eq(sendmsg(t, "nobody-we-know"), {})  -- not a member
  t:has(t:sw("a", "post", "cold", "later").stdout, "held, cold")  -- stored without a wake
  t:eq(t:sw("cold", "wait", "--timeout", "2", "--poll", "0.2", { ok = false }).code, 0)  -- non-urgent stays held
end

function T.test_session_turns_keep_cache_warm(t)
  t:agent("a")
  local now = os.time()
  t:fake("hc", ("#!/bin/sh\necho '{\"status_ms\": %d}'\n"):format((now - 60) * 1000))
  local kw = { status = "idle", ctx_tokens = 140000, last_active = now - 4 * 3600, compacted_at = 0 }
  t:agent("comms", kw); t:q("update agent set hc='t1' where name='comms'")
  t:agent("nohc", kw)
  t:eq(sendmsg(t, "comms"), {})
  t:eq(sendmsg(t, "nohc").permissionDecision, "deny")
  local who = t:sw("a", "who").stdout
  assert(who:find("comms idle [^\n]*idle=1m cache=warm") and not who:find("comms idle [^\n]*cache=warm COLD"), who)
  assert(who:find("nohc idle [^\n]*cache=cold COLD%-GUARDED"), who)
end

function T.test_wait_fenced_join_rebinds_dead_hc(t)
  t:agent("a")
  local now = os.time()
  t:fake("hc", ("#!/bin/sh\n[ \"$1\" = ls ] && echo '{\"terminals\": []}' && exit; [ \"$2\" = new ] && echo '{\"status_ms\": %d}' || echo '{}'\n")
    :format((now - 60) * 1000))
  t:agent("comms", { hc = "dead", status = "idle", ctx_tokens = 140000, last_active = now - 4 * 3600, compacted_at = 0 })
  t:sw("a", "post", "comms", "later")
  t:eq(t:sw("comms", "wait", "--timeout", "2", "--poll", "0.2", { ok = false }).code, 3)  -- outside Herdr while bound to "dead": fenced
  t:eq(t:sw("comms", "wait", "--timeout", "1", { ok = false, hc = "new" }).code, 3)  -- fenced: no rebind
  t:eq(t:q1("select hc from agent where name='comms'").hc, "dead")
  t:sw("comms", "join", { hc = "new" })  -- hc ls doesn't show dead live: join moves it without --takeover
  local w = t:sw("comms", "wait", "--timeout", "3", "--poll", "0.2", { ok = false, hc = "new" })
  t:eq(w.code, 2)
  t:has(w.stderr, "later")
  t:eq(t:q1("select hc from agent where name='comms'").hc, "new")
end

function T.test_urgent_override(t)
  t:agent("a")
  t:agent("cold", { status = "idle", ctx_tokens = 140000, last_active = os.time() - 4000, compacted_at = 0 })
  t:eq(sendmsg(t, "cold", "[urgent] main is red"), {})
  t:sw("a", "post", "cold", "--urgent", "stop pushing")
  local w = t:sw("cold", "wait", "--timeout", "3", "--poll", "0.2", { ok = false })
  t:eq(w.code, 2)
  t:has(w.stderr, "stop pushing")
  t:eq(t:q1("select data from event where kind='wake'").data, "1 msg urgent")
end

function T.test_wait_wakes_warm_idle(t)
  t:agent("a"); t:agent("b")
  t:sw("a", "post", "b", "ping")
  local w = t:sw("b", "wait", "--timeout", "3", "--poll", "0.2", { ok = false })
  t:eq(w.code, 2)
  t:has(w.stderr, "ping")
end

function T.test_prompt_hook_delivers_and_stops_waiter(t)
  t:agent("a"); t:agent("b")
  local w = bg(t, "b", "w.err", "wait", "--timeout", "10", "--poll", "0.2")
  sleep(1)
  t:eq(t:hook("b", "prompt", { prompt = "hi" }), {})  -- turn without a tool call: status -> working
  t:eq(reap(w, 5), 0)  -- old waiter exits; no double delivery
  t:sw("a", "post", "b", "while idle")
  t:has(t:hook("b", "prompt", { prompt = "x" }).additionalContext, "while idle")
  t:has(t:sw("b", "read").stdout, "no unread")
end

function T.test_newest_waiter_owns_inbox(t)
  t:agent("a"); t:agent("b")
  local w1 = bg(t, "b", "w1.err", "wait", "--timeout", "10", "--poll", "0.2")
  sleep(0.8)
  local w2 = bg(t, "b", "w2.err", "wait", "--timeout", "10", "--poll", "0.2")
  sleep(0.8)
  t:eq(reap(w1, 5), 0)  -- superseded without ever seeing 'working'
  t:has(t:sw("a", "post", "b", "ping").stdout, "wakes")
  t:eq(reap(w2, 5), 2)
  t:has(util.slurp(w2.errf), "ping")
  t:has(t:sw("a", "post", "b", "again").stdout, "no live waiter")
end

function T.test_post_to_comms_has_no_sendmessage_nudge(t)
  t:agent("a"); t:agent("x-comms", { status = "idle", last_active = os.time() })
  local out = t:sw("a", "post", "x-comms", "hi").stdout
  t:hasnt(out, "nudge by SendMessage")
  t:has(out, "held")
  t:agent("b", { status = "idle", last_active = os.time() })
  t:has(t:sw("a", "post", "b", "hi").stdout, "nudge by SendMessage")
end

function T.test_sendmessage_ref_and_hookless_waiter(t)
  t:agent("a")
  t:agent("cold", { status = "idle", ctx_tokens = 140000, last_active = os.time() - 4000, compacted_at = 0 })
  t:eq(sendmsg(t, "cold [ab12]").permissionDecision, "deny")
  t:sw("c", "join")  -- no hooks: idle, ctx 0 counts as cheap
  t:sw("a", "post", "c", "inbox")
  local w = t:sw("c", "wait", "--timeout", "3", "--poll", "0.2", { ok = false })
  t:eq(w.code, 2)
  t:has(w.stderr, "inbox")
end

function T.test_stop_hook_records_ctx(t)
  t:agent("a")
  local tr = t.d .. "/t.jsonl"
  put(tr, json.encode({ type = "assistant", message = { usage = {
    input_tokens = 10, cache_read_input_tokens = 90000, cache_creation_input_tokens = 500 } } }) .. "\n")
  t:hook("a", "stop", { transcript_path = tr })
  local r = t:q1("select status,ctx_tokens from agent where name='a'")
  t:eq({ r.status, r.ctx_tokens }, { "idle", 90510 })
  t:hook("a", "session", { source = "compact", transcript_path = tr })
  assert(t:q1("select compacted_at c from agent where name='a'").c > 0)
end

-- ---- board / state ----
function T.test_board_who(t)
  t:agent("a")
  t:sw("a", "task", "add", "do it")
  t:has(t:sw("a", "board").stdout, "do it")
  t:has(t:sw("a", "who").stdout, "a idle")
end

function T.test_state_json(t)
  t:eq(stj(t).active, false)
  assert(not exists(t.db), "read-only: no db is created")
  t:agent("a", { model = "opus", ctx_tokens = 90000 })
  t:agent("b")
  t:sw("a", "task", "add", "first")
  t:sw("a", "task", "add", "second", "--after", "1")
  t:sw("a", "task", "claim", "1")
  t:sw("a", "task", "block", "1", "which db?")
  t:sw("b", "lock", "b.txt")
  t:sw("a", "post", "b", "hello")
  t:sw("b", "leave")
  local before = t:q1("select count(*) n from event").n
  local s = stj(t)
  t:eq(t:q1("select count(*) n from event").n, before)
  assert(s.active)
  local t1, t2 = s.tasks[1], s.tasks[2]
  t:eq({ t1.state, t1.owner, t1.question }, { "blocked", "a", "which db?" })
  assert(t1.lease_left > 0)
  assert(t2.waiting)
  local a, b = s.agents[1], s.agents[2]
  t:eq({ a.name, a.status, a.model, a.ctx_tokens, a.cache }, { "a", "blocked", "opus", 90000, "warm" })
  t:eq(a.task.id, 1)
  t:eq(a.messages[1].body, "hello")
  t:eq({ b.name, b.status }, { "b", "ended" })
  t:eq(s.messages[1].dest, "b")
  local kinds = {}
  for i, e in ipairs(s.events) do kinds[i] = e.kind end
  t:has(kinds, "block")
  assert(s.machine ~= nil)
  t:sw("a", "post", "b", ("x"):rep(5000))
  t:eq(#stj(t).messages[1].body, 500)  -- long bodies (briefs) are cut
end

function T.test_state_json_round2(t)
  t:agent("a")
  t:q("update agent set status='idle', last_active=1000 where name='a'")
  t:q("update agent set wt=? where name='a'", t.repo)
  t:hook("a", "post-tool", { tool_name = "Bash", tool_input = { command = "git push" }, cwd = t.repo })
  t:q("update agent set status='idle', last_active=1000 where name='a'")
  t:q("insert or replace into event(ts,agent,kind,data) values(1,'a','push','git push old')")
  t:q("insert or replace into meta(k,v) values('comms','sr-comms')")
  local s = stj(t)
  local a = s.agents[1]
  t:eq({ s.comms, a.branch, a.cold_at }, { "sr-comms", "main", 1000 + 55 * 60 })
  local pushes = {}
  for _, e in ipairs(s.events) do if e.kind == "push" then pushes[#pushes + 1] = e end end
  t:eq({ pushes[1].branch, pushes[1].subject }, {})  -- older event
  t:eq({ pushes[2].branch, pushes[2].subject }, { "main", "init" })
  t:git(t.wt, "commit", "-q", "--allow-empty", "-m", "wt work")
  for _, cmd in ipairs({ "cd " .. t.wt .. " && git push", "git -C '" .. t.wt .. "' push", "cd ../wt; git push -u origin w2" }) do
    t:hook("a", "post-tool", { tool_name = "Bash", tool_input = { command = cmd }, cwd = t.repo })
  end
  pushes = {}
  for _, e in ipairs(stj(t).events) do
    if e.kind == "push" and #pushes < 3 then pushes[#pushes + 1] = { e.branch, e.subject } end  -- newest first
  end
  t:eq(pushes, { { "w2", "wt work" }, { "w2", "wt work" }, { "w2", "wt work" } })  -- the worktree's
end

function T.test_state_json_view(t)
  t:agent("a", { wt = t.wt })
  t:agent("b")
  t:sw("a", "task", "add", "t")
  t:sw("b", "lock", "b.txt")
  t:sw("a", "post", "b", "hi")
  t:sw("b", "leave")
  local function st(...) return stj(t, ...) end
  local function keys(s) local r = {} for k in pairs(s) do r[#r + 1] = k end table.sort(r) return r end
  local function union(...)
    local r = {}
    for _, l in ipairs({ ... }) do for _, k in ipairs(l) do r[#r + 1] = k end end
    table.sort(r)
    return r
  end
  local head = { "active", "db", "now", "comms", "tasks", "agents", "conflicts", "pressure", "machine" }
  -- "view" and "comms" are null in JSON where unset (decoded as absent), so compare what exists
  local views = { board = {}, activity = { "messages", "events" }, system = { "events", "locks", "running" },
                  overview = { "messages", "events" }, agents = {} }
  for view, extra in pairs(views) do
    local s = st("--view", view)
    local want = union(head, extra, { "view" })
    local got = keys(s)
    for i = #want, 1, -1 do if s[want[i]] == nil and (want[i] == "comms" or want[i] == "db") then table.remove(want, i) end end
    t:eq(got, want, view)
    local a, b = s.agents[1], s.agents[2]
    t:eq(a.messages, nil)  -- per-agent messages only for --agent
    t:eq(a.events ~= nil, view == "overview" or view == "agents" or view == "system", view)  -- live lanes
    t:eq(b.events, nil)  -- ended and not asked for
  end
  t:eq(st("--view", "board").tasks[1].title, "t")
  local a, b = unpack(st("--view", "agents", "--agent", "b").agents)
  t:eq({ b.messages[1].body, a.branch }, { "hi", "w2" })  -- w2: read from the worktree's HEAD
  local kinds = {}
  for i, e in ipairs(b.events) do kinds[i] = e.kind end
  t:has(kinds, "leave")
  local full = st()
  t:eq(full.view, nil)
  assert(full.agents[2].locks ~= nil, "no --view: everything, as before")
  for i = 0, 79 do t:q(("insert into event(ts,agent,kind,data) values(%d,'a','claim','#%d')"):format(i, i)) end
  assert(#st("--view", "activity").events > 80, "Activity reads further back")
  t:eq(#st("--view", "overview").events, 60)
end

-- ---- fake /proc ----
local function fake_proc(t, avail_kb, psi)
  avail_kb, psi = avail_kb or 20000000, psi or 1.0
  local r = t.d .. "/proc"
  os.execute("mkdir -p " .. r .. "/pressure")
  put(r .. "/uptime", "10000.0 0\n")
  put(r .. "/meminfo", ("MemTotal: 32000000 kB\nMemAvailable: %d kB\n"):format(avail_kb))
  for _, k in ipairs({ "memory", "cpu" }) do put(r .. "/pressure/" .. k, ("some avg10=%s avg60=0 avg300=0 total=0\n"):format(psi)) end
  return r
end

local function add_proc(r, pid, ppid, comm, argv, rss_pages, age_s)
  local d = r .. "/" .. pid
  os.execute("mkdir -p " .. d)
  local tck = unistd.sysconf(unistd._SC_CLK_TCK)
  local f = { "S", tostring(ppid) }
  for _ = 1, 17 do f[#f + 1] = "0" end
  f[#f + 1] = ("%d"):format((10000 - (age_s or 240)) * tck)
  f[#f + 1] = "0"
  f[#f + 1] = tostring(rss_pages or 0)
  put(d .. "/stat", ("%d (%s) "):format(pid, comm) .. table.concat(f, " "))
  put(d .. "/cmdline", table.concat(argv, "\0") .. "\0")
  put(d .. "/oom_score_adj", "0")
end

function T.test_state_json_running(t)
  local pr = fake_proc(t)
  t:hook("a", "session")
  t:q("update agent set claude_pid=100 where name='a'")
  add_proc(pr, 100, 1, "claude", { "claude" })
  add_proc(pr, 102, 100, "cabal", { "/x/bin/cabal", "build" }, 250000, 125)
  add_proc(pr, 200, 1, "node", { "node", "/x/bin/tsc", "-b" }, 125000)
  local function st(...)
    local args = { "a", "state", "--json", ... }
    args[#args + 1] = { env = { SWARM_PROC = pr } }
    return json.decode(t:sw(unpack(args)).stdout)
  end
  local got = {}
  for i, j in ipairs(st("--view", "system").running) do got[i] = { j.agent, j.command, j.elapsed_s, j.rss_kb } end
  t:eq(got, { { "a", "cabal build", 125, 1000000 }, { "other session", "tsc -b", 240, 500000 } })
  t:eq(st("--view", "board").running, nil)
end

function T.test_state_json_hc_only_where_shown(t)
  local now = os.time()
  local log = t.d .. "/hc.log"
  t:fake("hc", "#!/bin/sh\necho \"$2\" >> " .. log .. "\necho '{}'\n")
  local kw = { status = "idle", last_active = now - 4 * 3600 }
  t:agent("live", { hc = "t-live", status = kw.status, last_active = kw.last_active })
  t:agent("gone", { hc = "t-gone", status = kw.status, last_active = kw.last_active })
  t:q("update agent set ended=? where name='gone'", now)
  local function calls() local s = util.slurp(log); return s and util.splitlines(s) or {} end
  t:sw("a", "state", "--json", "--view", "board")
  t:eq(calls(), {})  -- board shows no idle timers
  t:sw("a", "state", "--json")
  t:eq(calls(), { "t-live" })  -- never an ended agent's terminal
end

function T.test_state_json_old_db(t)
  local c = sqlite3.open(t.db)  -- schema from before agent.wt / task.after,model,question
  assert(c:exec([[create table agent(name text primary key, hc text, model text, cwd text, status text, last_active int,
 ctx_tokens int default 0, compacted_at int default 0, started int, ended int, snap text, waiter int);
create table task(id integer primary key, title text, body text, state text, owner text, lease_until int,
 created_by text, evidence text);
create table msg(id integer primary key, ts int, frm text, dest text, body text, urgent int, kind text);
create table event(id integer primary key, ts int, agent text, kind text, path text, data text);
insert into agent(name,status,last_active) values('a','idle',1);
insert into task(title,state) values('t','open');]]) == sqlite3.OK)
  c:close()
  local s = stj(t)
  assert(s.active)
  t:eq({ s.agents[1].worktree, s.tasks[1].waiting }, { nil, false })
end

return T
