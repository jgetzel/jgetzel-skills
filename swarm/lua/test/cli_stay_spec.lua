-- `swarm stay`: an agent that says what it waits for is not ended by watchd (sw-roles §4, §8 item 2). Harness: cli.lua.
local json, util = require "swarm.json", require "swarm.util"
local unistd = require "posix.unistd"
local T = {}

local OLD = os.time() - 3600
local function comms_tick(t) t:sw("a", "watchd", "--once", "--comms", "comms", "--max-agents", "0") end
local function idle(t, name, kw)
  local o = { status = "idle", last_active = OLD, waiter = unistd.getpid() }  -- a live waiter
  for k, v in pairs(kw or {}) do o[k] = v end
  t:agent(name, o)
end
local function ended(t, name) return t:q1("select ended from agent where name=?", name).ended ~= nil end
local function stay(t, name) return t:q1("select stay from agent where name=?", name).stay end
local function digested(t, name) return #t:q("select 1 x from msg where dest=? and body like '%open task%'", name) end

-- idle, claimless and landed, but staying: neither ended nor digested; after --end it is ended
function T.test_stayer_not_ended_or_digested_until_end(t)
  idle(t, "comms"); idle(t, "e", { wt = t.wt, role = "reviewer" })
  t:has(t:sw("e", "stay", "PRs\nfor #130-#140", { cwd = t.wt }).stdout, "watchd won't end you")
  t:eq(stay(t, "e"), "PRs for #130-#140")  -- one line
  t:eq(t:q1("select data from event where kind='stay'").data, "PRs for #130-#140")
  t:sw("comms", "task", "add", "t1")
  comms_tick(t); comms_tick(t)
  assert(not ended(t, "e"), "a stayer was ended")
  t:eq(digested(t, "e"), 0)
  t:has(t:sw("e", "board").stdout, "staying: e reviewer: PRs for #130-#140")
  t:has(t:sw("e", "who").stdout, 'e idle role=reviewer stays: "PRs for #130-#140"')
  local st = json.decode(t:sw("a", "state", "--json").stdout)
  for _, x in ipairs(st.agents) do if x.name == "e" then t:eq(x.stay, "PRs for #130-#140") end end
  t:has(t:sw("e", "stay").stdout, "you stay for 'PRs for #130-#140'")
  t:sw("e", "stay", "--end")
  t:eq(stay(t, "e"), nil)
  t:eq(#t:q("select 1 x from event where kind='stay-end'"), 1)
  t:sw("comms", "task", "drop", "1")
  comms_tick(t)
  assert(ended(t, "e"), "no stay, landed and idle, yet not ended")
end

-- the text is cut at 80 characters, and an empty stay is refused
function T.test_stay_cut_and_empty_refused(t)
  t:agent("e")
  t:sw("e", "stay", ("x"):rep(100))
  t:eq(#stay(t, "e"), 80)
  t:has(t:sw("e", "stay", "  ", { ok = false }).stderr, "say what you wait for")
end

-- a stay is a self-write, fenced by terminal; it travels with the name through a takeover
function T.test_stay_fenced_and_kept_by_takeover(t)
  t:live_hc("t1", "t2")
  t:sw("e", "join", { hc = "t1" })
  t:sw("e", "stay", "reviews", { hc = "t1" })
  t:sw("e", "join", "--takeover", { hc = "t2" })
  t:eq(stay(t, "e"), "reviews")
  t:has(t:sw("e", "stay", "--end", { hc = "t1", ok = false }).stderr, "e is bound to t2")
  t:eq(stay(t, "e"), "reviews")
end

-- its terminal gone, reap ends a stayer and clears what it held
function T.test_reap_clears_stay(t)
  t:fakes()
  t:sw("e", "join", { hc = "t1" })
  t:sw("e", "stay", "reviews", { hc = "t1" })
  t:set_hc({ address = "t2" })
  t:sw("a", "watchd", "--once")
  assert(ended(t, "e"))
  t:eq(stay(t, "e"), nil)
end

-- stay protects the agent, not its claims: an idle stayer's expired claim reopens
function T.test_stayers_expired_claim_reopens(t)
  t:agent("e")
  t:sw("e", "stay", "reviews")
  t:sw("e", "task", "add", "t1"); t:sw("e", "task", "claim", "1")
  t:q("update task set lease_until=1")
  t:sw("a", "watchd", "--once")
  t:eq(t:q1("select state from task").state, "open")
  t:eq(stay(t, "e"), "reviews")
end

-- task done and the context note tell a stayer to keep staying and hand off what it holds, not to go idle and end
function T.test_stayer_done_line_and_ctx_note(t)
  t:agent("e")
  t:sw("e", "stay", "reviews")
  t:sw("e", "task", "add", "t1"); t:sw("e", "task", "claim", "1")
  local out = t:sw("e", "task", "done", "1", "--evidence", "x").stdout
  t:has(out, "you stay for 'reviews'")
  t:hasnt(out, "go idle")
  local tr = t.d .. "/t.jsonl"
  local f = assert(io.open(tr, "w"))
  f:write(json.encode({ type = "assistant", message = { usage = { input_tokens = 360000 } } }) .. "\n"); f:close()
  local s = ("st%d%d"):format(unistd.getpid(), math.random(1e9))
  local tmp = os.getenv("TMPDIR") or os.getenv("TEMP") or os.getenv("TMP") or "/tmp"
  t:defer(function() os.remove(tmp .. "/claude-ctx-" .. s) end)
  local ctx = t:hook("e", "post-tool", { tool_name = "Read", tool_input = {}, transcript_path = tr, session_id = s }).additionalContext
  t:has(ctx, "pass on what you hold")
  t:hasnt(ctx, "go idle")
end

-- the quiet notice (§8 item 3): on the edge into quiet, one message per stayer and one notice to comms; none on the
-- next tick; a new task re-arms it
local function to(t, name) return t:q("select body from msg where dest=? and body not like '%no waiter%'", name) end
function T.test_quiet_notice_once_per_edge(t)
  idle(t, "comms"); idle(t, "r", { stay = "PRs to review", role = "reviewer", last_active = os.time() - 60 })
  t:agent("w", { status = "working" })
  t:sw("comms", "task", "add", "t1"); t:sw("comms", "task", "drop", "1")
  comms_tick(t)
  t:eq(#to(t, "r"), 0)  -- w is still working: not quiet
  t:q("update agent set ended=1 where name='w'")
  comms_tick(t)
  t:eq(#to(t, "r"), 1)
  t:has(to(t, "r")[1].body, "You stay for: 'PRs to review'")
  t:eq(#to(t, "comms"), 1)
  t:has(to(t, "comms")[1].body, "r reviewer stays for 'PRs to review' (asked if that is over)")
  comms_tick(t)
  t:eq(#to(t, "r"), 1); t:eq(#to(t, "comms"), 1)
  t:sw("comms", "task", "add", "t2")
  comms_tick(t)
  t:eq(#to(t, "r"), 1)  -- a task is open: not quiet
  t:sw("comms", "task", "drop", "2")
  comms_tick(t)
  t:eq(#to(t, "r"), 2); t:eq(#to(t, "comms"), 2)
  t:eq(#t:q("select 1 x from event where kind='quiet'"), 2)
end

-- a cold or waiterless stayer is named to comms, not woken
function T.test_quiet_cold_or_waiterless_stayer_not_woken(t)
  local p = io.popen("sh -c 'echo $$'"); local dead = tonumber(p:read("*l")); p:close()
  idle(t, "comms")
  idle(t, "cold", { stay = "the plan", ctx_tokens = 140000, compacted_at = 0, last_active = os.time() - 72 * 60 })
  idle(t, "gone", { stay = "reviews", waiter = dead })
  t:sw("comms", "task", "add", "t1"); t:sw("comms", "task", "drop", "1")
  comms_tick(t)
  t:eq(#to(t, "cold"), 0); t:eq(#to(t, "gone"), 0)
  local n = to(t, "comms")
  t:eq(#n, 1)
  t:has(n[1].body, "cold stays for 'the plan' (cold, not woken)")
  t:has(n[1].body, "gone stays for 'reviews' (no live waiter, not woken)")
end

-- hung stayers (§8 item 13)
local function evs(t, kind) return #t:q("select 1 x from event where kind=?", kind) end
local function live(t, name) return #t:q("select 1 x from msg where dest=? and body like 'Liveness check:%'", name) end

function T.test_hung_waiterless_reported_once(t)
  local p = io.popen("sh -c 'echo $$'"); local dead = tonumber(p:read("*l")); p:close()
  idle(t, "comms"); idle(t, "g", { stay = "reviews", waiter = dead, last_active = os.time() - 60 })
  comms_tick(t); comms_tick(t)
  t:eq(#t:q("select 1 x from msg where dest='comms' and body like 'g stays for%can''t be woken%'"), 1)
  t:eq(evs(t, "stay-check"), 0)
end

function T.test_hung_unread_message_reported_once(t)
  idle(t, "comms"); idle(t, "r", { stay = "reviews", last_active = os.time() - 60 })
  t:sw("comms", "post", "r", "PR 5 is ready")
  comms_tick(t)
  t:eq(evs(t, "stay-unwoken"), 0)  -- not two ticks old yet
  t:q("update msg set ts=ts-120 where dest='r'")
  comms_tick(t); comms_tick(t)
  t:eq(evs(t, "stay-unwoken"), 1)
  t:eq(#t:q("select 1 x from msg where dest='comms' and body like 'r did not wake on a message%'"), 1)
end

-- board #28: a conflict notice never wakes a waiter, by design, so it is no sign of a hung stayer
function T.test_hung_notice_not_reported(t)
  idle(t, "comms"); idle(t, "r", { stay = "CI on PR #5", last_active = os.time() - 60 })
  t:q("insert into msg(ts,frm,dest,body,urgent,kind) values(?,'swarm','r','Your uncommitted work conflicts',0,'notice')",
    os.time() - 120)
  comms_tick(t); comms_tick(t)
  t:eq(evs(t, "stay-unwoken"), 0)
end

function T.test_liveness_check_hung_and_answered(t)
  idle(t, "comms")
  idle(t, "s", { stay = "the plan", last_active = os.time() - 49 * 60 })
  comms_tick(t)
  t:eq(live(t, "s"), 0)  -- not before 50 minutes
  t:q("update agent set last_active=? where name='s'", os.time() - 51 * 60)
  comms_tick(t); comms_tick(t)
  t:eq(live(t, "s"), 1)
  -- answered: last_active moved, no stay-hung; a new check goes out 50 idle minutes later
  t:q("update agent set last_active=? where name='s'", os.time())
  comms_tick(t)
  t:eq(evs(t, "stay-hung"), 0)
  t:q("update event set ts=ts-7200 where kind='stay-check'")  -- the answer came long ago; idle again for 51 min
  t:q("update agent set last_active=? where name='s'", os.time() - 51 * 60)
  comms_tick(t)
  t:eq(live(t, "s"), 2)
  -- unanswered five minutes on: one urgent stay-hung, then no more checks
  t:q("update event set ts=ts-400 where kind='stay-check' and id=(select max(id) from event where kind='stay-check')")
  comms_tick(t); comms_tick(t)
  t:eq(evs(t, "stay-hung"), 1)
  t:eq(#t:q("select 1 x from msg where dest='comms' and urgent=1 and body like 's stays for%liveness check%swarm nudge s`%'"), 1)
  t:eq(live(t, "s"), 2)
end

function T.test_communicator_never_checked(t)
  idle(t, "comms", { stay = "the user's channel", last_active = os.time() - 80 * 60 })
  comms_tick(t)
  t:eq(evs(t, "stay-check"), 0)
end

-- spawn --stay: a stayer before its first turn, with --task (at reserve) and without
function T.test_spawn_stay(t)
  t:fakes()
  t:sw("a", "task", "add", "do it")
  t:sw("a", "spawn", "t-8", "--stay", "PRs to review", "--task", "1")
  t:eq(stay(t, "t-8"), "PRs to review")
  t:sw("a", "spawn", "t-9", "--stay", "the plan", "--", "go")
  t:eq(stay(t, "t-9"), "the plan")
end

return T
