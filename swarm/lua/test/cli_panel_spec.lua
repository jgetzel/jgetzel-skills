-- The CLI the panel needs (REDESIGN.md §2, §3b): state --json's fate, ci and watchd; nudge; stay --end for another
-- agent; watchd --restart. Harness: cli.lua.
local json, util = require "swarm.json", require "swarm.util"
local unistd, wait, stdlib, fcntl = require "posix.unistd", require "posix.sys.wait", require "posix.stdlib", require "posix.fcntl"
local signal, ptime = require "posix.signal", require "posix.time"
local cli = require "test.cli"
local T = {}

local OLD = os.time() - 3600
local function sleep(s) ptime.nanosleep({ tv_sec = math.floor(s), tv_nsec = (s % 1) * 1e9 }) end
local function idle(t, name, kw)
  local o = { status = "idle", last_active = OLD, waiter = unistd.getpid() }  -- a live waiter
  for k, v in pairs(kw or {}) do o[k] = v end
  t:agent(name, o)
end
local function comms_tick(t) t:sw("a", "watchd", "--once", "--comms", "comms", "--max-agents", "0") end
local function st(t, ...) return json.decode(t:sw("a", "state", "--json", ...).stdout) end
local function by_name(s)
  local r = {}
  for _, x in ipairs(s.agents) do r[x.name] = x end
  return r
end
local function ended(t, name) return t:q1("select ended from agent where name=?", name).ended ~= nil end

-- fate is watchd's own verdict: what state --json says of each idle agent is what the next tick does to it
function T.test_fate_is_the_ticks_verdict(t)
  local uw = t.d .. "/wu"
  t:git(t.repo, "worktree", "add", "-q", "-b", "u1", uw)
  t:write("a", "../wu/new.txt", "scratch")  -- one uncommitted file
  idle(t, "comms")
  idle(t, "e", { wt = t.wt })                      -- small, a ready task, a live waiter: reuse
  idle(t, "u", { wt = uw })                        -- work not on its base: unclean
  idle(t, "s", { wt = t.wt, stay = "reviews" })    -- kept by its stay
  idle(t, "z", { wt = t.wt, waiter = 999999 })     -- small and a task ready, but no waiter: end
  idle(t, "w", { wt = t.wt, status = "working" })  -- not idle: no fate
  t:sw("comms", "task", "add", "t1")
  local a = by_name(st(t, "--view", "agents"))
  t:eq({ a.e.fate.verdict, a.e.fate.short, a.e.fate.says }, { "reuse", "#1 is ready", "Kept for reuse: #1 is ready" })
  t:eq({ a.u.fate.verdict, a.u.fate.short }, { "unclean", "uncommitted work" })
  t:eq({ a.s.fate.verdict, a.s.fate.short, a.s.fate.says }, { "kept", "stays", "Kept: stays" })
  t:eq({ a.z.fate.verdict, a.z.fate.short }, { "end", "ending" })
  t:eq(a.w.fate, nil)
  t:eq(#a.u.fate.checks, 0)  -- lanes: only the first reason
  -- every check for the one agent asked for, in the screen's order
  local u = by_name(st(t, "--view", "agents", "--agent", "u")).u.fate
  local labels, lit = {}, {}
  for i, c in ipairs(u.checks) do labels[i] = c.label; if c.on then lit[#lit + 1] = c.label end end
  t:eq(labels, { "Stays", "Holds a task", "Holds a lock", "Work not on its base", "Background process", "Unread messages",
    "Terminal", "Waiter", "Idle", "Context" })
  t:eq(lit, { "Work not on its base" })
  t:has(u.checks[4].detail, "1 uncommitted file, 0 commits not on")
  t:has(u.checks[9].detail, "watchd waits 2m")
  local e = by_name(st(t, "--agent", "e")).e.fate
  for _, c in ipairs(e.checks) do
    t:eq(c.on, c.label == "Context" or c.label == "Waiter", c.label)  -- reuse: the two that keep it together
  end
  -- the tick does what fate said
  comms_tick(t)
  t:eq({ ended(t, "e"), ended(t, "u"), ended(t, "s"), ended(t, "z"), ended(t, "w") }, { false, false, false, true, false })
  t:eq(#t:q("select 1 x from event where kind='digest' and agent='e'"), 1)
end

-- a held task and lock: the first reason fate stops at, with every check shown on --agent
function T.test_fate_held_task_and_lock(t)
  idle(t, "e", { wt = t.wt })
  t:sw("e", "task", "add", "t1"); t:sw("e", "task", "claim", "1"); t:sw("e", "lock", "b.txt")
  t:q("update agent set status='idle', last_active=? where name='e'", OLD)
  local f = by_name(st(t, "--view", "agents")).e.fate
  t:eq({ f.verdict, f.short }, { "kept", "holds #1" })
  f = by_name(st(t, "--agent", "e")).e.fate
  t:eq(f.says, "Kept: holds #1 and holds a lock")
  t:has(f.checks[2].detail, "#1 t1, lease ")
  t:eq(f.checks[3].detail, "b.txt")
end

-- ci: the latest runs on the base and the red streak; watchd: its record, liveness and whether code is newer
function T.test_state_ci_and_watchd(t)
  t:sw("a", "join")
  local function run(id, conc, created)
    t:q("insert into ci(id,sha,status,conclusion,url,created) values(?,?,?,?,?,?)", id, "s" .. id,
      conc and "completed" or "in_progress", conc, "u" .. id, created)
  end
  run(1, "success", "2026-01-01T00:00:01Z"); run(2, "failure", "2026-01-01T00:00:02Z")
  run(3, "cancelled", "2026-01-01T00:00:03Z"); run(4, "failure", "2026-01-01T00:00:04Z"); run(5, nil, "2026-01-01T00:00:05Z")
  local s = st(t)
  t:eq(s.ci.red_streak, 2)
  t:eq({ s.ci.runs[1].id, s.ci.runs[1].status, s.ci.runs[2].conclusion, s.ci.runs[2].url }, { 5, "in_progress", "failure", "u4" })
  t:eq(s.watchd, nil)
  t:q("insert into meta(k,v) values('watchd',?)", unistd.getpid() .. " t3")
  t:q("insert into meta(k,v) values('watchd_run',?)", json.encode({ flags = { "--comms", "c" }, cwd = t.repo, started = 1 }))
  s = st(t)
  t:eq({ s.watchd.pid, s.watchd.terminal, s.watchd.alive, s.watchd.stale, s.watchd.started, s.watchd.flags },
    { unistd.getpid(), "t3", true, true, 1, { "--comms", "c" } })
  t:q("update meta set v=? where k='watchd'", "999999 -")
  t:q("update meta set v=? where k='watchd_run'", json.encode({ flags = {}, cwd = t.repo, started = os.time() + 60 }))
  s = st(t)
  t:eq({ s.watchd.alive, s.watchd.stale, s.watchd.terminal }, { false, false, nil })
end

-- nudge types the one line into a live agent's terminal and logs it; an ended agent is refused, nothing sent
function T.test_nudge(t)
  t:fakes()
  t:sw("e", "join", { hc = "t1" })
  t:sw("f", "join", { hc = "t2" })
  t:sw("f", "leave", { hc = "t2" })
  local out = t:sw("x", "nudge", "e", { env = { SWARM_NAME = false } }).stdout
  t:has(out, "nudged e (t1)")
  t:has(t:calls("hc"), "send t1 read your messages and continue, or say what you wait for")
  t:eq(t:q1("select agent,path from event where kind='nudge'"), { agent = "human", path = "e" })
  t:has(t:sw("x", "nudge", "f", { ok = false }).stderr, "f has ended")
  t:has(t:sw("x", "nudge", "nobody", { ok = false }).stderr, "nobody is not an agent")
  t:eq(#t:q("select 1 x from event where kind='nudge'"), 1)
  -- nothing else moved: no message, no task, no stay
  t:eq(#t:q("select 1 x from msg"), 0)
end

-- stay --end NAME: human and the communicator may; anyone else is refused; watchd then ends it by the normal rules
function T.test_stay_end_for_another(t)
  idle(t, "comms")
  t:q("insert or replace into meta(k,v) values('comms','comms')")
  idle(t, "e", { wt = t.wt })
  t:sw("e", "stay", "reviews")
  t:q("update agent set last_active=? where name='e'", OLD)
  t:has(t:sw("p", "stay", "--end", "e", { ok = false }).stderr, "only human or the communicator")
  t:eq(t:q1("select stay from agent where name='e'").stay, "reviews")
  comms_tick(t)
  assert(not ended(t, "e"), "a stayer was ended")
  t:has(t:sw("x", "stay", "--end", "e", { env = { SWARM_NAME = false } }).stdout, "e's stay ended")
  t:eq(t:q1("select agent,path,data from event where kind='stay-end'"), { agent = "human", path = "e", data = "reviews" })
  t:has(t:sw("comms", "stay", "--end", "e", { ok = false }).stderr, "e stays for nothing")
  comms_tick(t)
  assert(ended(t, "e"), "no stay, landed and idle, yet not ended")
  t:has(t:sw("comms", "stay", "--end", "e", { ok = false }).stderr, "e is not a live agent")
end

-- ---- watchd --restart ----

-- an hc whose `run` starts the command after `--` in the background (or run.script instead), unless run.none exists
local function restart_hc(t)
  local D = util.shquote(t.d)
  t:fake("hc", "#!/bin/sh\necho \"$*\" >> " .. D .. "/hc.log\ncase \"$1\" in\nls) exit 1 ;;\nrun)\n"
    .. "  while [ \"$1\" != -- ]; do shift; done; shift\n"
    .. "  [ -f " .. D .. "/run.none ] && { echo '{\"address\":\"t9\"}'; exit 0; }\n"
    .. "  [ -f " .. D .. "/run.script ] && set -- sh " .. D .. "/run.script\n"
    .. "  nohup \"$@\" > " .. D .. "/new.out 2>&1 < /dev/null &\n  echo $! > " .. D .. "/new.pid\n"
    .. "  echo '{\"address\":\"t9\"}' ;;\n*) echo '{}' ;;\nesac\n")
  t:defer(function()
    local p = tonumber(util.slurp(t.d .. "/new.pid") or "")
    if p then signal.kill(p, signal.SIGTERM) end
  end)
end

-- the first watchd, in the background, as `swarm watchd` started by hand
local function first_watchd(t, ...)
  local pid = unistd.fork()
  if pid == 0 then
    local fd = fcntl.open(t.d .. "/old.err", fcntl.O_WRONLY + fcntl.O_CREAT + fcntl.O_TRUNC, 420)
    unistd.dup2(fd, 1); unistd.dup2(fd, 2)
    stdlib.setenv("SWARM_DB", t.db); stdlib.setenv("SWARM_NAME", "comms"); stdlib.setenv("HC_TERMINAL_ID", nil)
    stdlib.setenv("PATH", t.fakebin .. ":" .. cli.PATH)
    unistd.chdir(t.repo)
    unistd.execp(cli.SWARM, { "watchd", ... })
    unistd._exit(127)
  end
  t:defer(function() signal.kill(pid, signal.SIGTERM); pcall(wait.wait, pid) end)
  return pid
end
local function meta(t, k) local r = t:q1("select v from meta where k=?", k); return r and r.v end
local function until_(what, secs, f)
  for _ = 1, secs * 10 do
    if f() then return end
    sleep(0.1)
  end
  error("timed out waiting for " .. what)
end
local function exited(pid) local p = wait.wait(pid, wait.WNOHANG); return p ~= 0 end

function T.test_watchd_restart_same_flags_old_exits(t)
  restart_hc(t)
  t:sw("comms", "join")
  local old = first_watchd(t, "--interval", "1", "--comms", "comms", "--model", "haiku", "--max-agents", "2")
  until_("the first watchd's tick", 10, function() return meta(t, "watchd_up") == old .. " -" end)
  t:eq(json.decode(meta(t, "watchd_run")).flags, { "--interval", "1", "--min-free-mem", "4", "--comms", "comms", "--blocker-idle", "25", "--model", "haiku" })
  t:sw("a", "limits", "--min", "5")
  local r = t:sw("x", "watchd", "--restart", { env = { SWARM_NAME = false } })
  t:has(r.stdout, "watchd restarted: pid ")
  local new = tonumber(util.slurp(t.d .. "/new.pid"))
  t:eq(meta(t, "watchd"), new .. " -")
  t:eq(meta(t, "watchd_up"), new .. " -")
  until_("the old watchd to exit", 10, function() return exited(old) end)
  t:has(util.slurp(t.d .. "/old.err"), "was replaced by " .. new)
  local call
  for _, l in ipairs(t:calls("hc")) do if l:find("^run ") then call = l end end
  t:has(call, "run --json --bg --no-parent --no-notify --cwd " .. t.repo .. " -- ")
  t:has(call, "watchd --takeover --interval 1 --min-free-mem 4 --comms comms --blocker-idle 25 --model haiku")
  t:eq(meta(t, "agent_min"), "5")  -- --max-agents is not replayed over the user's number
  t:eq(st(t).watchd.pid, new)
end

-- a new watchd that never shows up: refused, the old one keeps the record and runs on
function T.test_watchd_restart_nothing_started(t)
  restart_hc(t)
  t:sw("comms", "join")
  local old = first_watchd(t, "--interval", "1", "--comms", "comms")
  until_("the first watchd's tick", 10, function() return meta(t, "watchd_up") == old .. " -" end)
  t:write("a", "../run.none", "")
  local r = t:sw("x", "watchd", "--restart", { ok = false, env = { SWARM_WATCHD_UP_WAIT = "2" } })
  t:eq(r.code, 1)
  t:has(r.stderr, ("no new watchd took over within 2 s; the old watchd (pid %d) still runs"):format(old))
  t:eq(meta(t, "watchd"), old .. " -")
  assert(not exited(old), "the old watchd exited")
end

-- one that takes the record and dies before its first tick: the record goes back and the old one runs on
function T.test_watchd_restart_new_dies(t)
  restart_hc(t)
  t:sw("comms", "join")
  local old = first_watchd(t, "--interval", "1", "--comms", "comms")
  until_("the first watchd's tick", 10, function() return meta(t, "watchd_up") == old .. " -" end)
  t:write("a", "../die.lua", ("require'lsqlite3'.open(%q):exec(\"update meta set v='999999 t9' where k='watchd'\")"):format(t.db))
  t:write("a", "../run.script", "luajit " .. util.shquote(t.d .. "/die.lua") .. "\n")
  local r = t:sw("x", "watchd", "--restart", { ok = false, env = { SWARM_WATCHD_UP_WAIT = "5" } })
  t:has(r.stderr, "watchd restart failed: the new watchd (999999 t9) died before its first tick; the old watchd")
  t:eq(meta(t, "watchd"), old .. " -")
  sleep(2)
  assert(not exited(old), "the old watchd exited")
  t:eq(meta(t, "watchd"), old .. " -")
end

-- the old watchd's side: replaced by a dead pid it takes the record back; by a live one that has not ticked, it waits
function T.test_watchd_hands_over_only_to_a_ticked_one(t)
  restart_hc(t)
  t:sw("comms", "join")
  local old = first_watchd(t, "--interval", "1", "--comms", "comms")
  until_("the first watchd's tick", 10, function() return meta(t, "watchd_up") == old .. " -" end)
  t:q("update meta set v='999999 t9' where k='watchd'")
  until_("the record back", 10, function() return meta(t, "watchd") == old .. " -" end)
  t:has(t:q1("select data from event where kind='watchd-back'").data, "999999 t9 died before its first tick")
  t:q("update meta set v=? where k='watchd'", unistd.getpid() .. " t9")  -- alive (this test), never ticked
  sleep(2.5)
  assert(not exited(old), "handed over to a watchd that never ticked")
  t:eq(meta(t, "watchd"), unistd.getpid() .. " t9")
  t:q("update meta set v=? where k='watchd_up'", unistd.getpid() .. " t9")
  until_("the old watchd to exit", 10, function() return exited(old) end)
end

return T
