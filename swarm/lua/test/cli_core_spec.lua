-- CLI tests ported from test_swarm.py (test_task_timing_columns .. test_shared_tree_notice_once): tasks, terminal
-- fencing, locks, messages, context notes, conflicts. Harness: cli.lua.
local json, util = require "swarm.json", require "swarm.util"
local sqlite3 = require "lsqlite3"
local unistd, wait, stdlib, fcntl = require "posix.unistd", require "posix.sys.wait", require "posix.stdlib", require "posix.fcntl"
local cli = require "test.cli"
local T = {}

local function state(t) return json.decode(t:sw("a", "state", "--json").stdout) end
local function count(s, sub) return select(2, s:gsub(sub, "")) end
local function tmpdir() return os.getenv("TMPDIR") or os.getenv("TEMP") or os.getenv("TMP") or "/tmp" end
local function sid(p) return ("%s%d%d%d"):format(p, unistd.getpid(), os.time(), math.random(1e9)) end
local function put(path, text) local f = assert(io.open(path, "w")); f:write(text); f:close() end

-- ---- tasks ----
function T.test_task_timing_columns(t)
  t:sw("a", "task", "add", "t1")
  t:sw("a", "task", "claim", "1")
  t:sw("a", "task", "block", "1", "why")
  t:sw("a", "task", "unblock", "1")
  t:has(t:sw("a", "task", "show", "1").stdout, "claims 1, releases 0, held by a")
  t:sw("a", "task", "done", "1", "--evidence", "e")
  local r = t:q1("select created_at, first_claimed_at, done_at from task")
  assert(r.created_at <= r.first_claimed_at and r.first_claimed_at <= r.done_at, cli.repr(r))
  local s = state(t).tasks[1]
  t:eq({ s.claims, s.holders, s.blocked_s >= 0 }, { 1, { "a" }, true })
  -- an older db: columns null, numbers come from the events
  t:q("update task set created_at=null, first_claimed_at=null, done_at=null")
  t:q("update event set ts=ts-100 where kind='task-add'")
  s = state(t).tasks[1]
  assert(s.queue_wait_s >= 100, s.queue_wait_s)
end

function T.test_timing_from_auto_spawn_event(t)
  t:sw("a", "task", "add", "t1")
  t:q("update task set state='done', owner='t-2', created_at=null")
  t:q("update event set ts=100 where kind='task-add'")
  t:q("insert into event(ts,agent,kind,data) values(160,'t-2','spawn','auto #1'),(400,'t-2','done','#1 e'),(5,'a','spawn','t-3')")
  local s = state(t).tasks[1]
  t:eq({ s.queue_wait_s, s.work_s, s.holders }, { 60, 240, { "t-2" } })
end

function T.test_task_show_and_claim_print_body(t)
  t:sw("a", "task", "add", "t1", "--body", "build X and Y")
  t:sw("a", "task", "add", "t2")
  t:has(t:sw("a", "board").stdout, "[body: task show]")
  t:has(t:sw("b", "task", "show", "1").stdout, "build X and Y")
  t:has(t:sw("a", "task", "claim", "1").stdout, "build X and Y")
  t:has(t:sw("a", "task", "show", "2").stdout, "(no body)")
end

function T.test_release_reopens(t)
  t:sw("a", "task", "add", "t1")
  t:sw("a", "task", "claim", "1")
  assert(t:sw("b", "task", "release", "1", { ok = false }).code ~= 0)
  t:sw("a", "task", "release", "1")
  t:eq(t:q1("select state,owner from task").state, "open")
  t:sw("b", "task", "claim", "1")
  t:eq(t:q1("select count(*) n from event where kind='release'").n, 1)
end

function T.test_lock_denial_logged(t)
  t:agent("a"); t:agent("b")
  t:sw("a", "lock", "a.txt")
  t:has(t:edit("b", "a.txt").permissionDecisionReason or "", "locked")
  t:eq(t:q1("select path,data from event where kind='deny-lock'").data, "a")
end

function T.test_claim_lease_done(t)
  t:sw("a", "task", "add", "t1")
  t:sw("a", "task", "claim", "1")
  assert(t:sw("b", "task", "claim", "1", { ok = false }).code ~= 0)
  t:eq(t:sw("a", "task", "done", "1", { ok = false }).code, 2)
  t:sw("a", "task", "renew", "1", "--lease", "3h")
  t:sw("a", "task", "done", "1", "--evidence", "sha abc")
  t:eq(t:q1("select state,evidence from task").state, "done")
end

function T.test_reaping(t)
  t:sw("a", "task", "add", "t1")
  t:sw("a", "task", "claim", "1")
  t:sw("b", "join")
  t:sw("a", "lock", "a.txt")
  t:q("update task set lease_until=1")
  t:q("update lock set lease_until=1")
  t:q("update agent set status='working' where name='a'")
  t:sw("a", "watchd", "--once")
  t:eq(t:q1("select state from task").state, "claimed")  -- live working owner: claim stays
  t:q("update agent set ended=1 where name='a'")
  t:sw("a", "watchd", "--once")
  t:eq(t:q1("select state from task").state, "open")
  t:eq(t:q("select * from lock"), {})
  t:has(t:sw("a", "read", { ok = false }).stderr, "was ended")  -- ended: only join returns it
  t:sw("a", "join")
  t:has(t:sw("a", "read").stdout, "lease")
  -- dead agent: hc terminal gone releases everything
  t:sw("a", "task", "claim", "1")
  t:sw("a", "lock", "b.txt")
  t:q("update agent set hc='t99' where name='a'")
  t:fakes(); t:set_hc({ address = "t1" })
  t:sw("a", "watchd", "--once")
  t:eq(t:q1("select count(*) n from event where kind='reap' and data='agent gone'").n, 1)
  t:eq(t:q1("select state from task").state, "open")
  t:eq(t:q("select * from lock"), {})
  assert(t:q1("select ended from agent where name='a'").ended ~= nil)
end

-- ---- fencing on the bound terminal (sw-ownership §7.2) ----
function T.test_other_terminal_hook_and_wait_dont_rebind(t)
  t:sw("a", "join", { hc = "t1" })
  t:q("update agent set status='idle'")
  local out = t:hook("a", "post-tool", { tool_name = "Bash", tool_input = { command = "ls" } }, "t2")
  t:has(out.additionalContext, "a is bound to t1; this terminal is t2. `swarm join --takeover`")
  t:eq(t:hook("a", "prompt", {}, "t2"), {})  -- said once per terminal
  t:eq(t:q1("select hc,status from agent"), { hc = "t1", status = "idle" })  -- wrote nothing
  local w = t:sw("a", "wait", "--timeout", "1", { hc = "t2", ok = false })
  t:eq({ w.code, util.strip(w.stderr) }, { 3, "a is bound to t1; this terminal is t2. `swarm join --takeover` moves it here." })
  t:eq(t:q1("select hc from agent").hc, "t1")
  t:has(t:sw("a", "task", "add", "x", { hc = "t2", ok = false }).stderr, "bound to t1")
  t:sw("a", "task", "add", "x", { hc = "t1" })
  t:sw("u", "join")  -- unbound row (outside Herdr): wait binds it
  t:sw("u", "wait", "--timeout", "1", { hc = "t3" })
  t:eq(t:q1("select hc from agent where name='u'").hc, "t3")
end

function T.test_ended_agent_not_revived(t)
  t:sw("a", "join", { hc = "t1" })
  t:sw("a", "leave", { hc = "t1" })
  t:has(t:hook("a", "prompt", {}, "t1").additionalContext, "a was ended at")
  t:hook("a", "stop", {}, "t1")
  local w = t:sw("a", "wait", "--timeout", "1", { hc = "t1", ok = false })
  t:eq(w.code, 3); t:has(w.stderr, "swarm join` to return")
  t:eq(t:q1("select status, ended is not null e from agent"), { status = "ended", e = 1 })
  t:has(t:sw("a", "lock", "a.txt", { hc = "t1", ok = false }).stderr, "swarm join` to return")
  t:sw("a", "join", { hc = "t1" })
  t:eq(t:q1("select status,ended from agent"), { status = "idle" })
end

function T.test_join_refused_on_live_binding_takeover_moves_and_logs(t)
  t:live_hc("t1", "t2")
  t:sw("a", "join", { hc = "t1" })
  t:sw("a", "task", "add", "t", { hc = "t1" }); t:sw("a", "task", "claim", "1", { hc = "t1" })
  local err = t:sw("a", "join", { hc = "t2", ok = false }).stderr
  t:has(err, "a is bound to t1; this terminal is t2. `swarm join --takeover`")
  t:eq(t:q1("select hc from agent").hc, "t1")
  -- relaunch: the predecessor t1 is still live, the successor takes over from t2
  t:sw("a", "join", "--takeover", { hc = "t2" })
  t:eq(t:q1("select hc from agent").hc, "t2")
  t:eq(t:q1("select data from event where kind='takeover'").data, "t1 -> t2")
  for _, cmd in ipairs({ { "task", "done", "1", "--evidence", "x" }, { "read" }, { "lock", "b.txt" }, { "post", "@all", "hi" } }) do
    cmd[#cmd + 1] = { hc = "t1", ok = false }
    t:has(t:sw("a", unpack(cmd)).stderr, "a is bound to t2; this terminal is t1", cmd[1])
  end
  t:has(t:hook("a", "pre-tool", { tool_name = "Bash", tool_input = { command = "ls" } }, "t1").additionalContext, "bound to t2")
  t:eq(t:q1("select state,owner from task"), { state = "claimed", owner = "a" })  -- the claim moved with the name
  t:sw("a", "task", "done", "1", "--evidence", "x", { hc = "t2" })
  -- a binding whose terminal hc ls doesn't show live moves without --takeover
  t:sw("b", "join", { hc = "t9" })
  t:sw("b", "join", { hc = "t2" })
  t:eq(t:q1("select hc from agent where name='b'").hc, "t2")
end

function T.test_takeover_then_predecessor_death_keeps_agent_claims_locks(t)
  t:fakes()
  t:sw("a", "join", { hc = "t1" })
  t:sw("a", "task", "add", "t", { hc = "t1" }); t:sw("a", "task", "claim", "1", { hc = "t1" })
  t:sw("a", "lock", "a.txt", { hc = "t1" })
  t:sw("a", "join", "--takeover", { hc = "t2" })
  t:set_hc({ address = "t2" })  -- the predecessor's terminal t1 is gone; only t2 is live
  t:sw("a", "watchd", "--once")
  t:eq(t:q1("select hc,ended from agent"), { hc = "t2" })
  t:eq(t:q1("select state from task").state, "claimed")
  t:eq(t:q1("select agent from lock").agent, "a")
end

function T.test_second_lock_on_held_path_refused(t)
  t:agent("a"); t:agent("b")
  t:sw("a", "lock", "a.txt")
  t:has(t:sw("b", "lock", "a.txt", { ok = false }).stderr, "locked by a")
  t:eq(t:q("select path,agent from lock"), { { path = "a.txt", agent = "a" } })
end

function T.test_concurrent_lock_waits_not_double_writes(t)
  t:agent("a"); t:agent("b")
  local peer = sqlite3.open(t.db)
  assert(peer:exec("begin immediate") == sqlite3.OK)
  local now = os.time()
  assert(peer:exec(("insert into lock(path,agent,since,lease_until) values('a.txt','a',%d,%d)"):format(now, now + 3600)) == sqlite3.OK)
  local errf = t.d .. "/lock.err"
  local pid = unistd.fork()
  if pid == 0 then
    local fd = fcntl.open(errf, fcntl.O_WRONLY + fcntl.O_CREAT + fcntl.O_TRUNC, 420)
    unistd.dup2(fd, 1); unistd.dup2(fd, 2)
    stdlib.setenv("SWARM_DB", t.db); stdlib.setenv("SWARM_NAME", "b"); stdlib.setenv("HC_TERMINAL_ID", nil)
    unistd.chdir(t.repo)
    unistd.execp(cli.SWARM, { "lock", "a.txt" })
    unistd._exit(127)
  end
  unistd.sleep(1)
  t:eq(select(2, wait.wait(pid, wait.WNOHANG)), "running")  -- waiting on the peer's transaction
  assert(peer:exec("commit") == sqlite3.OK)
  peer:close()
  local _, how, code = wait.wait(pid)
  assert(how == "exited" and code ~= 0, util.slurp(errf))
  t:eq(t:q("select path,agent from lock"), { { path = "a.txt", agent = "a" } })
end

function T.test_drop_claimed_only_by_owner_or_comms(t)
  for i = 0, 2 do t:sw("a", "task", "add", "t" .. i) end
  t:sw("a", "task", "claim", "1")
  t:sw("a", "task", "claim", "2")
  t:has(t:sw("b", "task", "drop", "1", { ok = false }).stderr, "only it or the communicator")
  t:sw("b", "task", "drop", "3")  -- open: anyone
  t:sw("a", "task", "drop", "1")
  t:sw("x-comms", "task", "drop", "2")
  t:eq(t:q("select state from task order by id"), { { state = "dropped" }, { state = "dropped" }, { state = "dropped" } })
end

-- ---- messages ----
function T.test_cursor(t)
  t:agent("a"); t:agent("b")
  t:sw("a", "post", "b", "hello")
  t:sw("a", "post", "@all", "all")
  t:has(t:sw("b", "read").stdout, "hello")
  t:has(t:sw("b", "read").stdout, "no unread")
  t:has(t:sw("a", "read").stdout, "no unread")  -- own @all not echoed
  t:sw("a", "post", "b", "again")
  t:has(t:sw("b", "read").stdout, "again")
end

function T.test_post_delivery_in_post_tool(t)
  t:agent("a"); t:agent("b")
  t:sw("a", "post", "b", "look at X")
  local out = t:hook("b", "post-tool", { tool_name = "Read", tool_input = {} })
  t:has(out.additionalContext, "look at X")
  t:eq(t:hook("b", "post-tool", { tool_name = "Read", tool_input = {} }), {})
end

function T.test_ctx_note_steps_marker_and_claim_refusal(t)
  t:agent("b")
  local tr = t.cwd.b .. "/t.jsonl"
  local function usage(n)
    put(tr, json.encode({ type = "assistant", message = { usage = { input_tokens = n } } }) .. "\n")
  end
  local s = sid("t")
  local mark = tmpdir() .. "/claude-ctx-" .. s
  local function post()
    return t:hook("b", "post-tool", { tool_name = "Read", tool_input = {}, transcript_path = tr, session_id = s })
  end
  t:defer(function() os.remove(mark) end)
  usage(300000)
  t:eq(post(), {})
  usage(360000)
  t:has(post().additionalContext, "go idle")
  t:eq(post(), {})  -- same step
  t:sw("b", "task", "add", "t1")
  assert(t:sw("b", "task", "claim", "1", { ok = false }).code ~= 0)
  usage(560000)
  t:has(post().additionalContext, "hand off now")
  put(mark, "9")  -- the repo hook already fired for this step
  usage(1000000 - 1)
  t:eq(post(), {})
end

function T.test_comms_ctx_note_from_commands(t)
  t:agent("x-comms")
  local s = sid("c")
  local home = t.d .. "/home/.claude/projects/p"
  os.execute("mkdir -p " .. util.shquote(home))
  put(home .. "/" .. s .. ".jsonl", json.encode({ type = "assistant", message = { usage = { input_tokens = 360000 } } }) .. "\n")
  local mark = tmpdir() .. "/claude-ctx-" .. s
  t:defer(function() os.remove(mark) end)
  local env = { HOME = t.d .. "/home", CLAUDE_CODE_SESSION_ID = s }
  t:has(t:sw("x-comms", "board", { env = env, ok = false }).stdout, "pass on the swarm")
  t:hasnt(t:sw("x-comms", "who", { env = env, ok = false }).stdout, "pass on the swarm")  -- once per step
end

function T.test_burst_capped_rest_stays_unread(t)
  t:agent("a"); t:agent("b")
  for i = 0, 39 do t:sw("a", "post", "b", "m" .. i .. " " .. ("y"):rep(400)) end
  local ctx = t:hook("b", "post-tool", { tool_name = "Read", tool_input = {} }).additionalContext
  assert(#ctx < 10000, #ctx)
  t:has(ctx, "more unread")
  local shown = count(ctx, " yyyy")
  local left = t:sw("b", "read").stdout
  t:eq(shown + count(left, " yyyy"), 40)
end

function T.test_new_agent_skips_older_broadcasts(t)
  t:agent("a")
  t:sw("a", "post", "@all", "old rule from another run")
  t:agent("b")  -- joins after it
  t:sw("a", "post", "@all", "new rule")
  t:sw("a", "post", "b", "for you")
  local out = t:sw("b", "read").stdout
  t:hasnt(out, "old rule")
  t:has(out, "new rule"); t:has(out, "for you")
  t:sw("b", "leave"); t:sw("a", "post", "@all", "while b was away")
  t:agent("b")  -- a rejoin keeps its cursor
  t:has(t:sw("b", "read").stdout, "while b was away")
end

function T.test_post_compact_ctx(t)
  local tr = t.d .. "/t.jsonl"
  put(tr, json.encode({ type = "assistant", message = { usage = { input_tokens = 1, cache_read_input_tokens = 200000 } } }) .. "\n"
    .. json.encode({ type = "system", compactMetadata = { postTokens = 9000 } }) .. "\n")
  t:agent("a")
  t:hook("a", "session", { source = "compact", transcript_path = tr })
  t:eq(t:q1("select ctx_tokens from agent where name='a'").ctx_tokens, 40000)
end

-- ---- conflicts ----
function T.test_compatible_appends_are_silent(t)
  t:agent("a"); t:agent("b")
  t:edit("a", "e.txt"); t:edit("b", "e.txt")
  t:write("a", "e.txt", "mod (p, q, c)\n")
  t:write("b", "e.txt", "mod (p, q, d)\n")
  t:tick()
  t:eq(t:q1("select count(*) n from msg where kind='notice'").n, 0)
  t:eq(t:q1("select count(*) n from event where kind='conflict-compat'").n, 1)
end

function T.test_same_token_episode(t)
  t:agent("a"); t:agent("b")
  t:edit("a", "a.txt"); t:edit("b", "a.txt")
  t:write("a", "a.txt", "y"); t:write("b", "a.txt", "z")
  t:tick()
  for _, p in ipairs({ { "a", "b" }, { "b", "a" } }) do
    local n = t:notices(p[1])
    t:eq(#n, 1)
    t:has(n[1].body, "conflicts with " .. p[2] .. "'s")
    t:has(n[1].body, "a.txt (your lines 1–1")
  end
  t:tick()
  t:eq(#t:notices("a"), 1)  -- same episode: silent
  t:write("b", "a.txt", "x")  -- revert one side
  t:tick()
  t:eq(t:q("select * from conflict"), {})
  t:write("b", "a.txt", "w")
  t:tick()
  t:eq(#t:notices("a"), 2)  -- a new episode
end

function T.test_fresh_worktree_off_origin_main_is_silent(t)
  t:agent("a"); t:agent("b")
  t:edit("b", "a.txt")
  t:write("b", "a.txt", "z")  -- b's own uncommitted edit, off the old main
  t:land("a.txt", "y")
  t.cwd.c = t.d .. "/wt3"
  t:git(t.repo, "worktree", "add", "-q", "-b", "c/x", t.cwd.c, "origin/main")
  t:agent("c")
  t:tick()
  t:eq(t:q1("select count(*) n from msg where kind='notice'").n, 0)
end

function T.test_merge_origin_main_is_silent(t)
  t:agent("a"); t:agent("b")
  local L = ""
  for i = 0, 8 do L = L .. "l" .. i .. "\n" end
  local function sub(s, a, b) return (s:gsub(a, b)) end
  t:write("a", "e.txt", L)
  t:git(t.repo, "commit", "-qam", "lines")
  t:git(t.wt, "merge", "-q", "main")
  t:land("e.txt", sub(L, "l0", "main0"))
  t.cwd.c = t.d .. "/wt3"
  t:git(t.repo, "worktree", "add", "-q", "-b", "c/x", t.cwd.c, "main")
  t:agent("c")
  t:edit("b", "e.txt"); t:edit("c", "e.txt")
  t:git(t.cwd.c, "merge", "-q", "origin/main")
  t:write("c", "e.txt", sub(sub(L, "l0", "main0"), "l8", "c8"))  -- c's own edit: line 8
  t:write("b", "e.txt", sub(L, "l0", "b0"))  -- b edits line 0, which main changed: b vs main, not vs c
  t:tick()
  t:eq(t:q1("select count(*) n from msg where kind='notice'").n, 0)
  t:write("b", "e.txt", sub(L, "l8", "b8"))  -- now b's own change overlaps c's
  t:tick()
  t:has(t:notices("c")[1].body, "conflicts with b's")
end

function T.test_shared_tree_notice_once(t)
  t.cwd.c = t.repo
  t:agent("a"); t:agent("c")
  t:eq(t:edit("a", "a.txt"), {})
  local out = t:edit("c", "a.txt")
  t:has(out.additionalContext, "also a's worktree")
  t:has(t:notices("a")[1].body, "also edits in")
  t:eq(t:edit("c", "a.txt"), {})
  t:edit("a", "b.txt")
  t:eq(#t:notices("a"), 1)
end

return T
