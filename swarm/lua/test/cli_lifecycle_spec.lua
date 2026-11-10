-- CLI tests ported from test_swarm.py (test_join_leave_who .. test_task_after_cycle_and_lines): join/leave, locks,
-- sweep, landed agents, digests, CI, block/unblock, task deps. test_lua_specs is run.lua itself. Harness: cli.lua.
local json, util = require "swarm.json", require "swarm.util"
local sqlite3 = require "lsqlite3"
local unistd, stdlib = require "posix.unistd", require "posix.stdlib"
local lfs = require "lfs"
local T = {}

local OLD = os.time() - 3600
local function sh(cmd, ...) return os.execute(cmd:format(...)) end
local function exists(p) return lfs.attributes(p) ~= nil end
local function rmtree(p) sh("rm -rf %s", util.shquote(p)) end
local function put(path, text) local f = assert(io.open(path, "w")); f:write(text); f:close() end
local function count(s, sub) return select(2, s:gsub(sub, "")) end
local function state(t) return json.decode(t:sw("a", "state", "--json").stdout) end
local function dirname(p) return p:match("^(.*)/[^/]*$") or "." end

local function comms_tick(t) t:sw("a", "watchd", "--once", "--comms", "comms", "--max-agents", "0") end
local function idle(t, name, kw)
  local o = { status = "idle", last_active = OLD, waiter = require("posix.unistd").getpid() }  -- a live waiter
  for k, v in pairs(kw or {}) do o[k] = v end
  t:agent(name, o)
end
local function ended(t, name) return t:q1("select ended from agent where name=?", name).ended ~= nil end
local function branches(t) return t:git(t.repo, "branch", "--list", "w2") end
local function commit_wip(t, name)
  t:write("b", name, "wip")
  t:git(t.wt, "add", ".")
  t:git(t.wt, "commit", "-qm", "wip")
end
-- same content, different commits, on w2 and main
local function squash(t)
  for _, who in ipairs({ "b", "a" }) do
    t:write(who, "a.txt", "squashed")
    t:git(t.cwd[who], "commit", "-qam", "change")
  end
end
local function old_wt(t, path)
  local gd = util.strip(t:git(path, "rev-parse", "--absolute-git-dir"))
  for _, p in ipairs({ path, gd .. "/logs/HEAD" }) do lfs.touch(p, OLD, OLD) end
end

local function fake_proc(t)
  local r = t.d .. "/proc"
  sh("mkdir -p %s/pressure", util.shquote(r))
  put(r .. "/uptime", "10000.0 0\n")
  put(r .. "/meminfo", "MemTotal: 32000000 kB\nMemAvailable: 20000000 kB\n")
  for _, k in ipairs({ "memory", "cpu" }) do put(r .. "/pressure/" .. k, "some avg10=1.0 avg60=0 avg300=0 total=0\n") end
  return r
end
local function add_proc(r, pid, ppid, comm, argv, cwd)
  local d = r .. "/" .. pid
  sh("mkdir -p %s", util.shquote(d))
  local f = { "S", tostring(ppid) }
  for _ = 1, 17 do f[#f + 1] = "0" end
  f[#f + 1] = tostring((10000 - 240) * 100); f[#f + 1] = "0"; f[#f + 1] = "0"  -- starttime (CLK_TCK 100), vsize, rss
  put(d .. "/stat", ("%d (%s) %s"):format(pid, comm, table.concat(f, " ")))
  put(d .. "/cmdline", table.concat(argv, "\0") .. "\0")
  put(d .. "/oom_score_adj", "0")
  if cwd then unistd.link(cwd, d .. "/cwd", true) end
end

-- ---- join, leave, who ----
function T.test_join_leave_who(t)
  t:live_hc("t1", "t2")
  t:sw("x", "join")
  t:q("insert into msg(ts,frm,dest,body) values(0,'x','@all','older run')")
  t:sw("a", "join", { hc = "t1" })
  t:eq(t:q1("select last_msg_id n from cursor where agent='a'").n, 1)  -- skips older broadcasts
  t:has(t:sw("a", "join", { hc = "t2", ok = false }).stderr, "a is bound to t1; this terminal is t2. `swarm join --takeover`")
  t:sw("a", "join", "--takeover", "--model", "opus", { hc = "t2" })
  local a = t:q1("select hc, model from agent where name='a'")
  t:eq({ a.hc, a.model }, { "t2", "opus" })
  t:eq(t:q1("select data from event where kind='takeover'").data, "t1 -> t2")
  t:eq(t:sw("a", "join", "p", "q", { ok = false }).code, 2)  -- bad usage
  t:sw("b", "join")
  t:q("insert into lock(path,agent,since,lease_until) values('x.txt','b',0,9999999999)")
  t:q("insert into task(title,state,owner,lease_until) values('t','claimed','b',9999999999)")
  t:q("update agent set ctx_tokens=52000 where name='b'")
  local who = t:sw("x", "who").stdout
  t:has(who, "machine: ")
  t:has(util.splitlines(who), "b idle ctx=52k idle=0m cache=warm wt: ? locks: x.txt")
  t:sw("x", "leave", "b")
  local b = t:q1("select status, ended is not null e from agent where name='b'")
  t:eq({ b.status, b.e }, { "ended", 1 })
  local tk = t:q1("select state, owner from task")
  t:eq({ tk.state, tk.owner, t:q("select * from lock") }, { "open", nil, {} })
  t:hasnt(t:sw("x", "who").stdout, "\nb ")
  t:has(t:sw("b", "leave", { ok = false }).stderr, "b was ended at")  -- fenced
  t:sw("b", "join")
  b = t:q1("select status, ended from agent where name='b'")
  t:eq({ b.status, b.ended }, { "idle", nil })
  local kinds = {}
  for _, r in ipairs(t:q("select kind from event where agent='b'")) do kinds[#kinds + 1] = r.kind end
  t:eq(kinds, { "join", "leave", "join" })
end

function T.test_who_flags_stale_herdr_copies(t)
  local home = stdlib.mkdtemp((os.getenv("TMPDIR") or "/tmp") .. "/swarm-home-XXXXXX")
  t:defer(function() rmtree(home) end)
  sh("mkdir -p %s/mods/jgetzel-tabs", util.shquote(home))
  local function run() return t:sw("x", "who", { env = { HERDR_APP_HOME = home } }).stdout end
  t:has(run(), "out of date: run install.sh")
  local stamp = t:exec({ "sh", "-c", "cat install.lua calendar/* ../swarm/herdr/mods/swarm/swarm.svg | sha256sum" },
    { cwd = dirname(require("test.cli").SWARM) .. "/../herdr-mods" }).stdout:match("%S+")
  put(home .. "/jgetzel-install.stamp", stamp .. "\n")
  t:hasnt(run(), "out of date")
end

function T.test_branch_fallback_for_wt(t)
  t:agent("w2"); t:q("update agent set wt=null")
  t:git(t.wt, "branch", "-m", "w2", "w2/x")
  t:has(t:sw("w2", "who").stdout, "wt: wt")
end

-- ---- locks ----
function T.test_lock_prefix_and_overlap(t)
  t:agent("a"); t:agent("b")
  t:sw("a", "lock", "migrations/0070*")
  t:eq(t:edit("b", "migrations/0070_x.sql").permissionDecision, "deny")
  t:sw("a", "lock", "docs/")
  t:eq(t:edit("b", "docs/x/y.md").permissionDecision, "deny")
  assert(t:sw("b", "lock", "docs/x.md", { ok = false }).code ~= 0)
  assert(t:sw("b", "lock", "migrations/0070_a.sql", { ok = false }).code ~= 0)
  t:sw("b", "lock", "other/")
  -- two globs neither of which covers the other can still share a file: m/a.lua (swarm/model: locksDisjoint)
  t:sw("a", "lock", "m/*.lua")
  assert(t:sw("b", "lock", "m/a*", { ok = false }).code ~= 0)
  t:sw("b", "lock", "m/*.txt")  -- no file ends in both .lua and .txt
end

function T.test_lock_released_when_work_lands(t)
  t:agent("a")
  t:edit("a", "a.txt")
  t:sw("a", "lock", "a.txt")
  t:tick()
  t:eq(#t:q("select * from lock"), 1)  -- no change yet: not seen
  t:write("a", "a.txt", "changed")
  t:tick()
  t:eq(t:q1("select seen from lock").seen, 1)
  t:git(t.repo, "commit", "-qam", "land")
  t:exec({ "git", "worktree", "prune" }, { cwd = t.repo })
  t:tick()  -- main moved to include the change: the file left a's working set
  t:eq(t:q("select * from lock"), {})
end

function T.test_bash_lock_violation(t)
  t:agent("a"); t:agent("b")
  t:edit("b", "b.txt")
  t:sw("a", "lock", "a.txt")
  t:write("b", "a.txt", "sneaky")
  t:tick()
  t:has(t:sw("b", "read").stdout, "violation")
  t:has(t:sw("a", "read").stdout, "locked path")
end

function T.test_hard_lock_deny(t)
  t:agent("a"); t:agent("b")
  t:sw("a", "lock", "*.txt", "--reason", "refactor")
  local out = t:edit("b", "a.txt")
  t:eq(out.permissionDecision, "deny")
  t:has(out.permissionDecisionReason, "locked by a")
  t:eq(t:edit("a", "a.txt"), {})
  t:sw("a", "unlock", "*.txt")
  t:eq(t:edit("b", "a.txt").permissionDecision, nil)
end

-- A lock typed in a subdirectory, or with ./, is the repo-relative path the edit hook sees.
function T.test_lock_path_is_repo_relative(t)
  t:agent("a"); t:agent("b")
  lfs.mkdir(t.cwd.a .. "/sub")
  t:has(t:sw("a", "lock", "x.txt", { cwd = t.cwd.a .. "/sub" }).stdout, "locked sub/x.txt")
  t:eq(t:edit("b", "sub/x.txt").permissionDecision, "deny")
  t:sw("a", "unlock", "./x.txt", { cwd = t.cwd.a .. "/sub" })
  t:eq(t:edit("b", "sub/x.txt").permissionDecision, nil)
  t:sw("a", "lock", "app/[id]/page.tsx")  -- glob characters in a literal path still cover that path
  t:eq(t:edit("b", "app/[id]/page.tsx").permissionDecision, "deny")
end

-- ---- sweep ----
function T.test_sweep(t)
  old_wt(t, t.wt)
  local pr = fake_proc(t)
  local function swp(...)
    local args = { "a", ... }
    args[#args + 1] = { env = { SWARM_PROC = pr } }
    return t:sw(unpack(args))
  end
  local function sweep() swp("watchd", "--once", "--comms", "comms", "--max-agents", "0") end
  t:has(swp("watchd", "--dry-run").stdout, t.wt)
  assert(exists(t.wt))
  add_proc(pr, 500, 1, "bash", { "bash" }, t.wt)
  sweep(); assert(exists(t.wt), "a process is in it")
  rmtree(pr .. "/500")
  t:agent("x", { cwd = t.wt .. "/sub" })
  sweep(); assert(exists(t.wt), "a live agent's cwd is in it")
  t:q("update agent set ended=1 where name='x'")
  t:write("b", "new.txt", "wip")
  old_wt(t, t.wt)
  sweep(); assert(exists(t.wt), "dirty")
  os.remove(t.wt .. "/new.txt")
  commit_wip(t, "u.txt")
  old_wt(t, t.wt)
  sweep(); assert(exists(t.wt), "unlanded")
  t:git(t.repo, "merge", "-q", "w2")
  lfs.touch(t.wt)
  sweep(); assert(exists(t.wt), "touched just now")
  old_wt(t, t.wt)
  sweep()
  assert(not exists(t.wt)); t:eq(branches(t), "")
  t:eq(t:q1("select count(*) n from event where kind='sweep'").n, 1)
  t:has(t:q1("select body from msg where kind='notice'").body, "swept 1")
end

function T.test_sweep_caches_not_landed(t)
  commit_wip(t, "u.txt")
  old_wt(t, t.wt)
  t:fakes(); t:set_gh("pr", "[]")
  local function asked() local n = 0; for _, x in ipairs(t:calls("gh")) do if x:find("^pr list") then n = n + 1 end end return n end
  local function ticks() local n = 0; for _, x in ipairs(t:calls("hc")) do if x:find("^ls") then n = n + 1 end end return n end
  local function tick(n)  -- n more ticks of the running watchd
    local goal = ticks() + n
    for _ = 1, 200 do
      if ticks() >= goal then return end
      os.execute("sleep 0.1")
    end
    error("watchd did not tick")
  end
  -- the verdict cache lives in the daemon: run it, not --once
  t:exec({ "sh", "-c", '"$0" watchd --comms comms --max-agents 0 --interval 1 >/dev/null 2>&1 </dev/null & echo $!',
    require("test.cli").SWARM }, { cwd = t.repo, env = { SWARM_DB = t.db, SWARM_NAME = "a", SWARM_PROC = fake_proc(t),
      PATH = t.fakebin .. ":" .. require("test.cli").PATH, HC_TERMINAL_ID = false } , stdout_file = t.d .. "/watchd.pid" })
  local pid = util.strip(util.slurp(t.d .. "/watchd.pid"))
  t:defer(function() sh("kill %s 2>/dev/null", pid) end)
  tick(1); tick(1); t:eq(asked(), 1)  -- unchanged: asked once over two ticks
  t:git(t.repo, "commit", "-q", "--allow-empty", "-m", "x")
  local no_origin = t:exec({ "git", "-C", t.repo, "remote", "get-url", "origin" }).code ~= 0 and 1 or 0
  tick(2); t:eq(asked(), 1 + no_origin)  -- B moved only when it is local main
  t:git(t.wt, "commit", "-q", "--allow-empty", "-m", "y")
  old_wt(t, t.wt)
  local n = asked(); tick(2); t:eq(asked(), n + 1)  -- HEAD moved
end

-- ---- landed agents ----
function T.test_landed_agent_ended_and_cleaned(t)
  idle(t, "e", { wt = t.wt })
  comms_tick(t)
  assert(ended(t, "e"))
  assert(not exists(t.wt))
  t:eq(branches(t), "")
  t:eq(t:q1("select data from event where kind='end'").data, "landed")
end

function T.test_squash_merged_agent_ended(t)
  idle(t, "e", { wt = t.wt })
  squash(t)
  comms_tick(t)
  assert(ended(t, "e"))
end

function T.test_dirty_or_unlanded_not_ended(t)
  idle(t, "e", { wt = t.wt })
  t:write("b", "new.txt", "wip")
  comms_tick(t)
  assert(not ended(t, "e"), "dirty")
  t:git(t.wt, "add", ".")
  t:git(t.wt, "commit", "-qm", "wip")
  comms_tick(t)
  assert(not ended(t, "e"), "clean but not on main")
  assert(exists(t.wt))
end

-- An idle agent kept only by an unclean worktree is told what holds it, once; idle again and still unclean, or with
-- no live waiter to wake, the communicator is told once instead.
local function nudges(t) return t:q("select body from msg where dest='e' and urgent=1") end
local function told(t) return t:q("select body from msg where dest='comms'") end

function T.test_unclean_agent_nudged_once_then_ended_when_clean(t)
  idle(t, "e", { wt = t.wt, last_active = os.time() - 600 })
  t:write("b", "scratch.txt", "x")
  comms_tick(t); t:eq(#nudges(t), 0)  -- idle under the threshold
  t:q("update agent set last_active=? where name='e'", OLD)
  comms_tick(t); comms_tick(t)
  t:eq(#nudges(t), 1)
  t:has(nudges(t)[1].body, "?? scratch.txt")
  t:eq(#told(t), 0)
  os.remove(t.wt .. "/scratch.txt")
  comms_tick(t)
  assert(ended(t, "e"), "cleaned up and not ended")
end

function T.test_nudged_and_still_unclean_tells_comms_once(t)
  idle(t, "e", { wt = t.wt })
  commit_wip(t, "new.txt")
  comms_tick(t); t:eq(#nudges(t), 1)
  t:has(nudges(t)[1].body, "wip")
  t:q("update event set ts=ts-5000")  -- e woke after the nudge and is idle again, still holding the commit
  comms_tick(t); comms_tick(t)
  t:eq(#nudges(t), 1)
  t:eq(#told(t), 1)
  t:has(told(t)[1].body, "wip")
  assert(not ended(t, "e"))
end

function T.test_unclean_agent_without_waiter_tells_comms(t)
  local p = io.popen("sh -c 'echo $$'"); local dead = tonumber(p:read("*l")); p:close()
  idle(t, "e", { wt = t.wt, waiter = dead })
  t:write("b", "scratch.txt", "x")
  comms_tick(t); comms_tick(t)
  t:eq(#nudges(t), 0)
  t:eq(#told(t), 1)
  t:has(told(t)[1].body, "?? scratch.txt")
end

function T.test_missing_worktree(t)
  idle(t, "e", { wt = t.wt })
  rmtree(t.wt)  -- branch w2 still registered; its commits are on main
  comms_tick(t)
  assert(ended(t, "e"))
  idle(t, "f", { wt = t.wt .. "-gone" })  -- no worktree, no branch
  comms_tick(t)
  assert(ended(t, "f"))
end

function T.test_missing_worktree_unlanded_branch_not_ended(t)
  idle(t, "e", { wt = t.wt })
  commit_wip(t, "new.txt")
  rmtree(t.wt)
  comms_tick(t)
  assert(not ended(t, "e"))
end

function T.test_missing_worktree_squash_merged_branch_ended(t)
  t:fakes()
  idle(t, "e", { wt = t.wt })
  squash(t)
  rmtree(t.wt)
  comms_tick(t)
  assert(ended(t, "e"))
end

-- A merged PR counts only when it merged this commit: a branch reused after its PR merged holds new work.
function T.test_merged_pr_of_reused_branch_not_ended(t)
  t:fakes()
  idle(t, "e", { wt = t.wt })
  commit_wip(t, "new.txt")
  t:set_gh("pr", { { number = 1, headRefOid = "0000000000000000000000000000000000000000" } })
  comms_tick(t)
  assert(not ended(t, "e"), "the merged PR was an earlier commit")
  assert(exists(t.wt))
  t:set_gh("pr", { { number = 2, headRefOid = util.strip(t:git(t.wt, "rev-parse", "HEAD")) } })
  comms_tick(t)
  assert(ended(t, "e"), "the merged PR is this commit")
end

function T.test_end_agent_keeps_worktree_a_live_peer_uses(t)
  t:fakes()
  idle(t, "e", { wt = t.wt })
  t:agent("p", { wt = t.wt })
  comms_tick(t)
  assert(ended(t, "e"))
  assert(exists(t.wt))
end

function T.test_idle_owner_past_lease_loses_claim(t)
  idle(t, "e", { wt = t.wt })
  t:sw("e", "task", "add", "t"); t:sw("e", "task", "claim", "1")
  t:q("update task set lease_until=1")
  comms_tick(t)
  assert(not ended(t, "e"))
  t:eq(t:q1("select state from task").state, "open")
  t:has(t:sw("e", "read").stdout, "lease expired while idle")
end

function T.test_working_owner_past_lease_keeps_claim(t)
  t:fakes()
  t:agent("e", { status = "working" }); t:agent("comms")
  t:sw("e", "task", "add", "t"); t:sw("e", "task", "claim", "1")
  t:q("update task set lease_until=1")
  comms_tick(t)
  t:eq(t:q1("select state from task").state, "claimed")
  t:has(t:sw("comms", "read").stdout, "past its lease")
  comms_tick(t)
  t:eq(t:q1("select count(*) n from msg where dest='comms'").n, 1)  -- once per lease period
end

function T.test_prompt_blocked_owner_past_lease_keeps_claim(t)
  t:fakes()
  t:agent("e", { status = "blocked" }); t:agent("comms")
  t:sw("e", "task", "add", "t"); t:sw("e", "task", "claim", "1")
  t:q("update task set lease_until=1")
  comms_tick(t)
  t:eq(t:q1("select state from task").state, "claimed")
end

function T.test_comms_never_digested_or_ended_reusable_digested(t)
  idle(t, "comms"); idle(t, "r")
  t:sw("comms", "task", "add", "t")
  comms_tick(t)
  assert(not ended(t, "comms")); assert(not ended(t, "r"))
  t:has(t:sw("r", "read").stdout, "1 open task")
  t:hasnt(t:sw("comms", "read").stdout, "open task")
end

function T.test_digest_edge_triggered(t)
  idle(t, "comms"); idle(t, "r")
  local function digests() return #t:q("select 1 x from msg where dest='r' and body like '%open task%'") end
  t:sw("comms", "task", "add", "t1")
  comms_tick(t); t:eq(digests(), 1)
  t:q("update event set ts=ts-5000"); t:q("update agent set last_active=last_active-5000")
  comms_tick(t); t:eq(digests(), 1)  -- unchanged pool, 900 s later: silent
  t:sw("comms", "task", "add", "t2")
  comms_tick(t); t:eq(digests(), 2)  -- a new id
  t:sw("comms", "task", "claim", "2"); t:sw("comms", "task", "block", "2", "q")
  t:sw("comms", "task", "add", "t3", "--after", "2")  -- waits on a blocked task: not startable
  comms_tick(t); t:eq(digests(), 2)
end

-- A reusable agent that has read a digest naming every startable task and is idle again had its chance: it is
-- ended, not kept as a reason to spawn no one. Else a task that reopens after the agent was told of it waits for good
-- (swarm/model: l_after, L1).
function T.test_reusable_agent_told_and_idle_again_is_ended(t)
  t:fakes()
  idle(t, "comms"); idle(t, "r")
  t:sw("comms", "task", "add", "t1")
  comms_tick(t)
  t:has(t:sw("r", "read").stdout, "1 open task")  -- r wakes, reads it, and stops without taking #1
  t:q("update agent set status='idle', last_active=? where name='r'", OLD)
  comms_tick(t)
  assert(ended(t, "r"), "r, told of #1 and idle again, still holds the slot")
  t:sw("comms", "watchd", "--once", "--comms", "comms", "--max-agents", "1", "--min-free-mem", "0")
  t:eq(t:q1("select state from task where id=1").state, "claimed")  -- the freed slot is filled for #1
end

-- An idle agent whose waiter exited (swarm wait timed out) never reads a digest: it is ended, not kept as a reason to
-- spawn no one (swarm/model: l_after_waiter, L1 and L3).
function T.test_reusable_agent_with_dead_waiter_is_ended(t)
  t:fakes()
  local p = io.popen("sh -c 'echo $$'"); local dead = tonumber(p:read("*l")); p:close()
  idle(t, "comms"); idle(t, "r", { waiter = dead })
  t:sw("comms", "task", "add", "t1")
  comms_tick(t)
  assert(ended(t, "r"), "r can't wake, yet holds the slot")
  t:sw("comms", "watchd", "--once", "--comms", "comms", "--max-agents", "1", "--min-free-mem", "0")
  t:eq(t:q1("select state from task where id=1").state, "claimed")
end

function T.test_big_context_finished_even_with_open_tasks(t)
  idle(t, "big", { ctx_tokens = 120000 })
  t:sw("big", "task", "add", "t")
  comms_tick(t)
  assert(ended(t, "big"))
end

function T.test_task_done_says_what_next(t)
  t:agent("a", { ctx_tokens = 20000 })
  for _, x in ipairs({ "x", "y", "z" }) do t:sw("a", "task", "add", x) end
  t:sw("a", "task", "claim", "1")
  t:has(t:sw("a", "task", "done", "1", "--evidence", "e").stdout, "take the next task")
  t:q("update agent set ctx_tokens=120000")
  t:sw("a", "task", "claim", "2")
  t:has(t:sw("a", "task", "done", "2", "--evidence", "e").stdout, "go idle")
end

-- ---- CI ----
function T.test_pr_ci_merge_to_green(t)
  t:fakes()
  t:agent("a")
  t:sw("a", "task", "add", "t1"); t:sw("a", "task", "claim", "1")
  t:sw("a", "task", "done", "1", "--evidence", "PR #7 merged")
  t:set_gh("pr", { { number = 7, mergedAt = "2026-11-08T10:00:00Z", mergeCommit = { oid = "red" }, headRefName = "a/x" } })
  for i, r in ipairs({ { "red", "failure", "2026-11-08T10:00:05Z", "2026-11-08T10:02:00Z" },
                       { "fix", "success", "2026-11-08T10:05:00Z", "2026-11-08T10:08:00Z" } }) do
    t:q("insert into ci(id,sha,status,conclusion,created,updated) values(?,?,'completed',?,?,?)", i, r[1], r[2], r[3], r[4])
  end
  local function prs() local n = 0; for _, x in ipairs(t:calls("gh")) do if x:find("^pr ") then n = n + 1 end end return n end
  t:sw("a", "watchd", "--once", "--ci")
  local s = state(t).tasks[1]
  t:eq({ s.pr, s.ci_conclusion, s.merge_to_green_s }, { 7, "failure", 480 })
  t:has(t:sw("a", "task", "show", "1").stdout, "PR #7 merged")
  t:eq(prs(), 1)  -- runs come from the ci table, not GitHub
  t:sw("a", "watchd", "--once", "--ci")
  t:eq(prs(), 1)  -- the PR list is asked for at most every 10 minutes
end

function T.test_ci_poll_once_for_all(t)
  t:fakes()
  t:agent("a")
  t:set_gh("api", { { databaseId = 1, headSha = "a1", status = "completed", conclusion = "failure", url = "u1",
                      createdAt = "2026-11-08T10:00:00Z", updatedAt = "2026-11-08T10:03:00Z", event = "push" } })
  t:set_gh("run", "server, e2e\n")
  local function subs()  -- the poll's own calls
    local r = {}
    for _, x in ipairs(t:calls("gh")) do
      if x:find("^api") or x:find("--json jobs", 1, true) then r[#r + 1] = x:match("%S+") end
    end
    return r
  end
  t:sw("a", "watchd", "--once", "--ci")
  t:eq(subs(), { "api", "run" })  -- one request for the runs, one for the red run's jobs
  local c = t:q1("select conclusion, failed from ci where id=1")
  t:eq({ c.conclusion, c.failed }, { "failure", "server, e2e" })
  t:sw("a", "watchd", "--once", "--ci")
  t:eq(#subs(), 2)  -- within the minute: no call
  t:q("update meta set v='0' where k='ci_polled'")
  t:set_gh("api", nil)  -- rate limited
  t:sw("a", "watchd", "--once", "--ci")
  t:eq(#t:q("select 1 x from ci"), 1)  -- kept
  assert(t:q1("select 1 x from meta where k='ci_error'"))
end

function T.test_ci_reads_the_table(t)
  local function sha() return util.strip(t:git(t.repo, "rev-parse", "HEAD")) end
  local function commit() t:git(t.repo, "commit", "-q", "--allow-empty", "-m", "c") end
  local c1 = sha(); commit(); local c2 = sha(); commit(); local c3 = sha()
  t:sw("a", "join")
  t:eq(count(t:sw("a", "ci", c1, "--wait", "--timeout", "2", "--poll", "1", { ok = false }).stderr, "nobody is polling"), 1)
  t:q("insert into meta(k,v) values('ci_polled',?)", tostring(os.time()))
  t:eq(t:sw("a", "ci", c1, { ok = false }).code, 2)  -- no run yet
  t:q("insert into ci(id,sha,status,conclusion,url,created) values(1,?,'completed','cancelled','u','2026-11-08T10:00:00Z')", c2)  -- replaced by the next push
  t:q("insert into ci(id,sha,status,conclusion,url,created) values(2,?,'in_progress',null,'u','2026-11-08T10:01:00Z')", c3)
  t:eq(t:sw("a", "ci", c1, { ok = false }).code, 2)  -- c3's run includes c1, still running
  t:q("update ci set status='completed', conclusion='failure', failed='e2e' where id=2")
  local r = t:sw("a", "ci", c1, { ok = false })
  t:eq(r.code, 1)
  t:has(r.stdout, "failed: e2e")
  t:q("insert into ci(id,sha,status,conclusion,url,created) values(3,?,'completed','success','u','2026-11-08T10:05:00Z')", c3)  -- a re-run, green
  t:eq(t:sw("a", "ci", c2).code, 0)
  t:eq(t:sw("a", "ci", c3, "--wait", "--timeout", "5").code, 0)
end

-- ---- block, unblock ----
function T.test_block_unblock(t)
  t:fakes()
  t:agent("a"); t:agent("t-comms")
  t:sw("a", "task", "add", "t1"); t:sw("a", "task", "claim", "1")
  t:sw("b", "task", "block", "1", "q?", { ok = false })
  t:sw("a", "task", "block", "1", "which db?")
  t:has(t:sw("a", "board").stdout, "#1 blocked by a: which db?")
  t:q("update task set lease_until=1")
  for _ = 1, 2 do t:sw("a", "watchd", "--once", "--comms", "t-comms", "--max-agents", "0") end
  t:eq(t:q1("select state,owner from task").state, "blocked")
  t:eq(#t:q("select 1 x from msg where dest='t-comms' and body like '%which db?%'"), 1)
  t:sw("b", "task", "unblock", "1", { ok = false })
  t:sw("t-comms", "task", "unblock", "1", "--answer", "sqlite")
  t:eq(t:q1("select state,owner from task").owner, "a")
  t:eq(t:q1("select state from task").state, "claimed")
  t:eq(#t:q("select 1 x from msg where dest='a' and body like '%sqlite%'"), 1)
  t:has(t:sw("a", "task", "show", "1").stdout, "sqlite")
  -- the answer outlives the owner: a second agent claiming the released task sees it
  t:sw("a", "task", "release", "1"); t:agent("c")
  t:has(t:sw("c", "task", "claim", "1").stdout .. t:sw("c", "task", "show", "1").stdout, "sqlite")
end

function T.test_hc_blocked_marks_task(t)
  t:fakes()
  t:set_hc({ address = "h1", status = "blocked" })
  t:agent("a", { hc = "h1", status = "working" }); t:agent("t-comms")
  t:sw("a", "task", "add", "t1", { hc = "h1" }); t:sw("a", "task", "claim", "1", { hc = "h1" })
  local function tick() t:sw("a", "watchd", "--once", "--comms", "t-comms", "--max-agents", "0") end
  tick()
  t:eq(t:q1("select state from task").state, "blocked")
  t:eq(#t:q("select 1 x from msg where dest='t-comms'"), 1)  -- one notice, not two
  t:set_hc({ address = "h1", status = "working" })
  tick()
  t:eq(t:q1("select state from task").state, "claimed")
end

-- ---- task deps ----
function T.test_after_dependency(t)
  t:agent("a")
  t:sw("a", "task", "add", "first"); t:sw("a", "task", "add", "second", "--after", "1")
  t:has(t:sw("a", "board").stdout, "after #1")
  local r = t:sw("a", "task", "claim", "2", { ok = false })
  assert(r.code ~= 0)
  t:has(r.stderr, "waits on #1")
  t:sw("a", "task", "claim", "1"); t:sw("a", "task", "done", "1", "--evidence", "e")
  t:sw("a", "task", "claim", "2")
end

function T.test_deps_migration(t)
  local h = assert(sqlite3.open(t.db))  -- a task.after from before task.deps
  assert(h:exec("create table task(id integer primary key, title text, body text, state text default 'open', owner text,"
    .. " lease_until int, created_by text, evidence text, after int);"
    .. "insert into task(title) values('one'); insert into task(title,after) values('two',1);") == sqlite3.OK)
  h:close()
  t:agent("a")
  local rows = t:q("select deps from task")
  t:eq({ rows[1].deps, rows[2].deps }, { nil, "1" })
  for _, c in ipairs(t:q("pragma table_info(task)")) do assert(c.name ~= "after", "after column left") end
  t:has(t:sw("a", "board").stdout, "after #1  two")
end

function T.test_deps_list_holds_until_last_done(t)
  t:fakes()
  t:agent("a")
  for _, x in ipairs({ "one", "two", "three" }) do t:sw("a", "task", "add", x) end
  t:sw("a", "task", "add", "four", "--after", "3,1")
  t:eq(t:q1("select deps from task where id=4").deps, "3,1")
  local function check(ready)
    local ids, has4 = {}, false
    for _, x in ipairs(state(t).tasks) do
      if x.state == "open" and not x.waiting then ids[#ids + 1] = x.id end
    end
    table.sort(ids)
    t:eq(ids, ready)
    for _, id in ipairs(ready) do has4 = has4 or id == 4 end
    if not has4 then
      t:has(t:sw("a", "task", "claim", "4", { ok = false }).stderr, "waits on")
      t:has(t:sw("a", "spawn", "t-9", "--task", "4", { ok = false }).stderr, "waits on")
    end
  end
  check({ 1, 2, 3 })
  for _, step in ipairs({ { 1, { 2, 3 } }, { 2, { 3 } }, { 3, { 4 } } }) do
    t:sw("a", "task", "claim", tostring(step[1])); t:sw("a", "task", "done", tostring(step[1]), "--evidence", "e")
    check(step[2])
  end
  t:has(t:sw("a", "task", "show", "4").stdout, "after: #3 done, #1 done")
  t:sw("a", "task", "claim", "4")
  t:has(t:sw("a", "task", "add", "x", "--after", "1,9", { ok = false }).stderr, "no task #9")
end

function T.test_task_after_cycle_and_lines(t)
  t:agent("a")
  for _, x in ipairs({ "one", "two", "three" }) do t:sw("a", "task", "add", x) end
  t:sw("a", "task", "after", "2", "1")
  t:sw("a", "task", "after", "3", "2,1")
  local r = t:sw("a", "task", "after", "1", "3", { ok = false })
  t:has(r.stderr, "#1 → #3 → #2 → #1")
  t:has(t:sw("a", "task", "after", "1", "1", { ok = false }).stderr, "#1 → #1")
  t:has(t:sw("a", "board").stdout, "after #1  two")
  local show = t:sw("a", "task", "show", "1").stdout
  t:has(show, "blocks: #2, #3")
  t:hasnt(show, "after:")
  t:has(t:sw("a", "task", "show", "3").stdout, "after: #2 open, #1 open")
  local s = {}
  for _, x in ipairs(state(t).tasks) do s[x.id] = x end
  t:eq({ s[3].deps, s[1].blocks, s[3].blocks }, { { 2, 1 }, { 2, 3 }, {} })
  local out = t:sw("a", "task", "drop", "1").stdout
  t:has(out, "#2 waits on #1: drop it too, or `swarm task after 2 …`")
  t:has(out, "#3 waits on #1")
  t:has(t:sw("a", "board").stdout, "after #2, #1 (dropped)  three")  -- still held back
  t:sw("a", "task", "after", "3", "")  -- cleared
  t:eq(t:q1("select deps from task where id=3").deps, "")
  t:sw("a", "task", "claim", "2", { ok = false })
  t:sw("a", "task", "claim", "3")
  t:has(t:sw("a", "task", "after", "3", "2", { ok = false }).stderr, "is claimed")
end

return T
