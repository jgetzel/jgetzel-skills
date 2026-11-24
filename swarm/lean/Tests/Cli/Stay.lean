import Tests.Cli.Fixture

/-! cli_stay_spec.lua: `swarm stay`: an agent that says what it waits for is not ended by watchd (sw-roles §4, §8 item 2). -/

namespace SwarmLean.Tests.Cli.Stay
open SwarmLean.Tests.Cli
open SwarmLean.Sqlite (Val)
open Lean (Json toJson)

def now : IO Int := return ((← SwarmLean.Sqlite.now).toNat : Int)
def comms_tick (t : T) : IO Unit :=
  t.sw_ "a" ["watchd", "--once", "--comms", "comms", "--max-agents", "0"]
/-- An idle agent with a live waiter (this process), old; `kw` overrides. -/
def idle (t : T) (name : String) (kw : List (String × Val) := []) : IO Unit := do
  let old := (← now) - 3600
  let pid : Int := (← IO.Process.getPID).toNat
  let base : List (String × Val) := [("status", "idle"), ("last_active", .int old), ("waiter", .int pid)]
  t.agent name (base.filter (fun (k, _) => !kw.any (·.1 == k)) ++ kw)
def ended (t : T) (name : String) : IO Bool :=
  return (← t.q1 "select ended from agent where name=?" [.text name]).f "ended" != .null
def stay (t : T) (name : String) : IO Json :=
  return (← t.q1 "select stay from agent where name=?" [.text name]).f "stay"
def digested (t : T) (name : String) : IO Nat :=
  return (← t.q "select 1 x from msg where dest=? and body like '%Related tasks%'" [.text name]).size
/-- The pid of a process that has exited. -/
def deadPid : IO Int := do
  let r ← IO.Process.output { cmd := "sh", args := #["-c", "echo $$"] }
  return ((strip r.stdout).toNat?.getD 0 : Nat)

-- idle, claimless and landed, but staying: neither ended nor digested; after --end it is ended
def test_stayer_not_ended_or_digested_until_end (t : T) : IO Unit := do
  idle t "comms"; idle t "e" [("wt", t.wt), ("role", "reviewer")]
  has (← t.sw "e" ["stay", "PRs\nfor #130-#140"] { cwd := some t.wt }).stdout "watchd won't end you"
  eq (← stay t "e") "PRs for #130-#140"  -- one line
  eq ((← t.q1 "select data from event where kind='stay'").f "data") "PRs for #130-#140"
  t.sw_ "comms" ["task", "add", "t1"]
  comms_tick t; comms_tick t
  unless !(← ended t "e") do fail "a stayer was ended"
  eq (← digested t "e") 0
  has (← t.sw "e" ["board"]).stdout "staying: e reviewer: PRs for #130-#140"
  has (← t.sw "e" ["who"]).stdout "e idle role=reviewer stays: \"PRs for #130-#140\""
  let st ← match Json.parse (← t.sw "a" ["state", "--json"]).stdout with
    | .ok j => pure j | .error e => fail s!"state --json: {e}"
  for x in ((st.f "agents").getArr?.toOption.getD #[]) do
    if x.f "name" == "e" then eq (x.f "stay") "PRs for #130-#140"
  has (← t.sw "e" ["stay"]).stdout "you stay for 'PRs for #130-#140'"
  t.sw_ "e" ["stay", "--end"]
  eq (← stay t "e") Json.null
  eq (← t.q "select 1 x from event where kind='stay-end'").size 1
  t.sw_ "comms" ["task", "drop", "1"]
  comms_tick t
  unless ← ended t "e" do fail "no stay, landed and idle, yet not ended"

-- the text is cut at 80 characters, and an empty stay is refused
def test_stay_cut_and_empty_refused (t : T) : IO Unit := do
  t.agent "e"
  t.sw_ "e" ["stay", "".pushn 'x' 100]
  eq ((← stay t "e").s?.getD "").utf8ByteSize 80
  has (← t.sw "e" ["stay", "  "] { ok := false }).stderr "say what you wait for"

-- a stay is a self-write, fenced by terminal; it travels with the name through a takeover
def test_stay_fenced_and_kept_by_takeover (t : T) : IO Unit := do
  t.liveHc ["t1", "t2"]
  t.sw_ "e" ["join"] { hc := some "t1" }
  t.sw_ "e" ["stay", "reviews"] { hc := some "t1" }
  t.sw_ "e" ["join", "--takeover"] { hc := some "t2" }
  eq (← stay t "e") "reviews"
  has (← t.sw "e" ["stay", "--end"] { hc := some "t1", ok := false }).stderr "e is bound to t2"
  eq (← stay t "e") "reviews"

-- its terminal gone, reap ends a stayer and clears what it held
def test_reap_clears_stay (t : T) : IO Unit := do
  t.fakes
  t.sw_ "e" ["join"] { hc := some "t1" }
  t.sw_ "e" ["stay", "reviews"] { hc := some "t1" }
  t.setHc [json% {"address": "t2"}]
  t.sw_ "a" ["watchd", "--once"]
  unless ← ended t "e" do fail "e not ended"
  eq (← stay t "e") Json.null

-- stay protects the agent, not its claims: an idle stayer's expired claim reopens
def test_stayers_expired_claim_reopens (t : T) : IO Unit := do
  t.agent "e"
  t.sw_ "e" ["stay", "reviews"]
  t.sw_ "e" ["task", "add", "t1"]; t.sw_ "e" ["task", "claim", "1"]
  t.q_ "update task set lease_until=1"
  t.sw_ "a" ["watchd", "--once"]
  eq ((← t.q1 "select state from task").f "state") "ready"
  eq (← stay t "e") "reviews"

-- task done and the context note tell a stayer to keep staying and keep what it holds, not to go idle and end
def test_stayer_done_line (t : T) : IO Unit := do
  t.agent "e"
  t.sw_ "e" ["stay", "reviews"]
  t.sw_ "e" ["task", "add", "t1"]; t.sw_ "e" ["task", "claim", "1"]
  let out := (← t.sw "e" ["task", "done", "1", "--evidence", "x"]).stdout
  has out "you stay for 'reviews'"
  hasnt out "go idle"

-- the quiet notice (§8 item 3): on the edge into quiet, one message per stayer and one notice to comms; none on the
-- next tick; a new task re-arms it
def to (t : T) (name : String) : IO (Array Json) :=  -- not the host's memory pressure notice (board #141)
  t.q "select body from msg where dest=? and body not like '%no waiter%' and body not like 'memory pressure:%'"
    [.text name]
def test_quiet_notice_once_per_edge (t : T) : IO Unit := do
  idle t "comms"; idle t "r" [("stay", "PRs to review"), ("role", "reviewer"), ("last_active", .int ((← now) - 60))]
  t.agent "w" [("status", "working")]
  t.sw_ "comms" ["task", "add", "t1"]; t.sw_ "comms" ["task", "drop", "1"]
  comms_tick t
  eq (← to t "r").size 0  -- w is still working: not quiet
  t.q_ "update agent set ended=1 where name='w'"
  comms_tick t
  eq (← to t "r").size 1
  has (((← to t "r")[0]!).f "body") "You stay for: 'PRs to review'"
  eq (← to t "comms").size 1
  has (((← to t "comms")[0]!).f "body") "r reviewer stays for 'PRs to review' (asked if that is over)"
  comms_tick t
  eq (← to t "r").size 1; eq (← to t "comms").size 1
  t.sw_ "comms" ["task", "add", "t2"]
  comms_tick t
  eq (← to t "r").size 1  -- a task is open: not quiet
  t.sw_ "comms" ["task", "drop", "2"]
  comms_tick t
  eq (← to t "r").size 2; eq (← to t "comms").size 2
  eq (← t.q "select 1 x from event where kind='quiet'").size 2

-- a cold or waiterless stayer is named to comms, not woken
def test_quiet_cold_or_waiterless_stayer_not_woken (t : T) : IO Unit := do
  let dead ← deadPid
  idle t "comms"
  idle t "cold" [("stay", "the plan"), ("ctx_tokens", 140000), ("compacted_at", 0), ("last_active", .int ((← now) - 72 * 60))]
  idle t "gone" [("stay", "reviews"), ("waiter", .int dead)]
  t.sw_ "comms" ["task", "add", "t1"]; t.sw_ "comms" ["task", "drop", "1"]
  comms_tick t
  eq (← to t "cold").size 0; eq (← to t "gone").size 0
  let n ← to t "comms"
  eq n.size 1
  has ((n[0]!).f "body") "cold stays for 'the plan' (cold, not woken)"
  has ((n[0]!).f "body") "gone stays for 'reviews' (no live waiter, not woken)"

-- hung stayers (§8 item 13)
def evs (t : T) (kind : String) : IO Nat := return (← t.q "select 1 x from event where kind=?" [.text kind]).size
def live (t : T) (name : String) : IO Nat :=
  return (← t.q "select 1 x from msg where dest=? and body like 'Liveness check:%'" [.text name]).size

def test_hung_waiterless_reported_once (t : T) : IO Unit := do
  let dead ← deadPid
  idle t "comms"; idle t "g" [("stay", "reviews"), ("waiter", .int dead), ("last_active", .int ((← now) - 60))]
  comms_tick t; comms_tick t
  eq (← t.q "select 1 x from msg where dest='comms' and body like 'g stays for%can''t be woken%'").size 1
  eq (← evs t "stay-check") 0

-- board #191: a compaction the swarm asked for kills the waiter and no Stop follows it; no report until watchd's
-- continue line went out (or the hold ran out), and `post` says it is compacting
def test_hung_not_while_compacting (t : T) : IO Unit := do
  let dead ← deadPid
  let nw : IO Nat := return (← t.q "select 1 x from msg where dest='comms' and body like 'g stays for%can''t be woken%'").size
  idle t "comms"; idle t "g" [("stay", "compacting, then #7"), ("waiter", .int dead), ("last_active", .int ((← now) - 60))]
  t.q_ "insert into event(ts, agent, kind) values (strftime('%s','now') - 70, 'g', 'compact-asked')" []
  comms_tick t
  eq (← nw) 0
  has (← t.sw "comms" ["post", "g", "hi"]).stdout "g: compacting (watchd wakes it when that ends)"
  t.q_ "insert into event(ts, agent, kind) values (strftime('%s','now'), 'g', 'compact')" []
  comms_tick t
  eq (← nw) 0  -- ended, the continue line not yet sent
  t.q_ "insert into event(ts, agent, kind) values (strftime('%s','now'), 'g', 'ctx-continue')" []
  comms_tick t
  eq (← nw) 1
  has (← t.sw "comms" ["post", "g", "hi"]).stdout "g: no live waiter"
  -- a compaction asked long ago no longer holds the report
  idle t "h" [("stay", "reviews"), ("waiter", .int dead), ("last_active", .int ((← now) - 60))]
  t.q_ "insert into event(ts, agent, kind) values (strftime('%s','now') - 700, 'h', 'ctx-compact')" []
  comms_tick t
  eq (← t.q "select 1 x from msg where dest='comms' and body like 'h stays for%can''t be woken%'").size 1

def test_hung_unread_message_reported_once (t : T) : IO Unit := do
  idle t "comms"; idle t "r" [("stay", "reviews"), ("last_active", .int ((← now) - 60))]
  t.sw_ "comms" ["post", "r", "PR 5 is ready"]
  comms_tick t
  eq (← evs t "stay-unwoken") 0  -- not two ticks old yet
  t.q_ "update msg set ts=ts-120 where dest='r'"
  comms_tick t; comms_tick t
  eq (← evs t "stay-unwoken") 1
  eq (← t.q "select 1 x from msg where dest='comms' and body like 'r did not wake on a message%'").size 1

-- board #28: a conflict notice never wakes a waiter, by design, so it is no sign of a hung stayer
def test_hung_notice_not_reported (t : T) : IO Unit := do
  idle t "comms"; idle t "r" [("stay", "CI on PR #5"), ("last_active", .int ((← now) - 60))]
  t.q_ "insert into msg(ts,frm,dest,body,urgent,kind) values(?,'swarm','r','Your uncommitted work conflicts',0,'notice')"
    [.int ((← now) - 120)]
  comms_tick t; comms_tick t
  eq (← evs t "stay-unwoken") 0

def test_liveness_check_hung_and_answered (t : T) : IO Unit := do
  idle t "comms"
  idle t "s" [("stay", "the plan"), ("last_active", .int ((← now) - 14 * 60))]
  comms_tick t
  eq (← live t "s") 0  -- a free-text stay: not before 15 minutes
  t.q_ "update agent set last_active=? where name='s'" [.int ((← now) - 16 * 60)]
  comms_tick t; comms_tick t
  eq (← live t "s") 1
  let m := ((← t.q1 "select body from msg where dest='s' and body like 'Liveness check:%'").f "body").s?.getD ""
  has m "What exactly are you waiting for?"
  has m "If you can take any step now, take it and `swarm stay --end`"
  has m "`swarm stay \"<why>\" --until <cond>`"
  hasnt m "do nothing"
  -- answered: last_active moved, no stay-hung; a new check goes out 50 idle minutes later
  t.q_ "update agent set last_active=? where name='s'" [.int (← now)]
  comms_tick t
  eq (← evs t "stay-hung") 0
  t.q_ "update event set ts=ts-7200 where kind='stay-check'"  -- the answer came long ago; idle again for 51 min
  t.q_ "update agent set last_active=? where name='s'" [.int ((← now) - 30 * 60)]
  comms_tick t
  eq (← live t "s") 1  -- after the first check each 50 minutes, not 15
  t.q_ "update agent set last_active=? where name='s'" [.int ((← now) - 51 * 60)]
  comms_tick t
  eq (← live t "s") 2
  -- unanswered five minutes on: one urgent stay-hung, then no more checks
  t.q_ "update event set ts=ts-400 where kind='stay-check' and id=(select max(id) from event where kind='stay-check')"
  comms_tick t; comms_tick t
  eq (← evs t "stay-hung") 1
  eq (← t.q "select 1 x from msg where dest='comms' and urgent=1 and body like 's stays for%liveness check%swarm nudge s`%'").size 1
  eq (← live t "s") 2

-- board #193: a live holder keeps its lapsed claim; it is told first, the communicator only after its next idle
/-- Agent `name` joined on hc terminal `h` (hc lists it), idle an hour, with a live waiter; it adds and claims #1, whose
lease has lapsed. -/
def holder (t : T) (name h : String) : IO Unit := do
  t.fakes
  t.sw_ name ["join"] { hc := some h }
  t.setHc [json% {"address": $(h)}]
  t.q_ "update agent set status='idle', last_active=?, waiter=? where name=?"
    [.int ((← now) - 3600), .int (← IO.Process.getPID).toNat, .text name]
  t.sw_ name ["task", "add", "t1"] { hc := some h }; t.sw_ name ["task", "claim", "1"] { hc := some h }
  t.q_ "update task set lease_until=?" [.int ((← now) - 60)]
  t.q_ "update agent set last_active=? where name=?" [.int ((← now) - 3600), .text name]
def taskState (t : T) : IO Json := return (← t.q1 "select state from task where id=1").f "state"
def leaseMsgs (t : T) (dest pat : String) : IO Nat :=
  return (← t.q "select 1 x from msg where dest=? and body like ?" [.text dest, .text pat]).size

def test_compacting_holder_keeps_claim (t : T) : IO Unit := do
  idle t "comms"; holder t "e" "t1"
  t.q_ "insert into event(ts, agent, kind) values (strftime('%s','now') - 10, 'e', 'compact-asked')" []
  comms_tick t
  eq (← taskState t) "in_progress"
  t.q_ "insert into event(ts, agent, kind) values (strftime('%s','now'), 'e', 'compact')" []
  comms_tick t
  eq (← taskState t) "in_progress"
  t.q_ "insert into event(ts, agent, kind) values (strftime('%s','now'), 'e', 'ctx-continue')" []
  comms_tick t
  eq (← taskState t) "in_progress"
  t.q_ "update agent set status='working', last_active=? where name='e'" [.int (← now)]
  comms_tick t
  t.q_ "update agent set status='idle' where name='e'"
  comms_tick t
  eq (← taskState t) "in_progress"
  eq (← evs t "reap") 0

-- an owner with no terminal does not live (`Watchd.lives`): only the compaction keeps its lapsed claim
def test_compacting_unbound_owner_keeps_claim_until_continue (t : T) : IO Unit := do
  idle t "comms"; idle t "e"
  t.sw_ "e" ["task", "add", "t1"]; t.sw_ "e" ["task", "claim", "1"]
  t.q_ "update task set lease_until=?" [.int ((← now) - 60)]
  t.q_ "update agent set status='idle', last_active=? where name='e'" [.int ((← now) - 30)]
  t.q_ "insert into event(ts, agent, kind) values (strftime('%s','now') - 10, 'e', 'compact-asked')" []
  comms_tick t
  eq (← taskState t) "in_progress"
  t.q_ "insert into event(ts, agent, kind) values (strftime('%s','now'), 'e', 'compact')" []
  comms_tick t
  eq (← taskState t) "in_progress"
  t.q_ "insert into event(ts, agent, kind) values (strftime('%s','now'), 'e', 'ctx-continue')" []
  comms_tick t
  eq (← taskState t) "ready"

-- a cold holder (a big context, idle past the prompt cache) is woken by an urgent notice; one with a job is not hung
def test_cold_holder_woken_urgent (t : T) : IO Unit := do
  idle t "comms"; holder t "e" "t1"
  t.q_ "update agent set ctx_tokens=300000 where name='e'"
  comms_tick t
  eq (← t.q "select 1 x from msg where dest='e' and urgent=1 and body like 'Your lease on #1 ended%'").size 1

def test_live_idle_holder_keeps_claim_and_is_told (t : T) : IO Unit := do
  idle t "comms"; holder t "e" "t1"
  comms_tick t
  eq (← taskState t) "in_progress"
  eq (← leaseMsgs t "e" "Your lease on #1 ended at %; `swarm task renew 1`%") 1
  eq (← leaseMsgs t "comms" "%past its lease%") 0  -- not before the holder's next idle
  comms_tick t
  eq (← leaseMsgs t "e" "Your lease on #1 ended%") 1  -- once per lease
  -- it woke, did not renew, and is idle again: the communicator is told, once
  t.q_ "update agent set last_active=? where name='e'" [.int ((← now) + 5)]
  comms_tick t; comms_tick t
  eq (← taskState t) "in_progress"
  eq (← leaseMsgs t "comms" "e has held #1 past its lease%did not renew%") 1
  eq (← evs t "stay-hung") 0

def test_hung_holder_claim_reopens (t : T) : IO Unit := do
  idle t "comms"; holder t "e" "t1"
  comms_tick t
  eq (← taskState t) "in_progress"
  -- the notice went unanswered LIVENESS_WAIT: hung, and the next reap reopens it
  t.q_ "update event set ts=ts-400 where kind='lease-late'"
  comms_tick t
  eq (← evs t "stay-hung") 1
  comms_tick t
  eq (← taskState t) "ready"
  eq (← leaseMsgs t "comms" "#1 reopened: e is hung%") 1
  -- a stayer flagged hung by its own liveness check loses its lapsed claim too
  t.sw_ "e" ["task", "claim", "1"] { hc := some "t1" }
  t.q_ "update task set lease_until=?" [.int ((← now) - 60)]
  t.q_ "update agent set status='idle', stay='reviews', last_active=? where name='e'" [.int ((← now) - 60)]
  t.q_ "insert into event(ts, agent, kind) values (strftime('%s','now'), 'e', 'stay-hung')" []
  comms_tick t
  eq (← taskState t) "ready"

def test_ended_holder_claim_released (t : T) : IO Unit := do
  idle t "comms"; holder t "e" "t1"
  t.sw_ "e" ["leave"] { hc := some "t1" }
  eq (← taskState t) "ready"
  -- a holder whose terminal hc no longer lists is reaped as gone, its claim released
  t.sw_ "f" ["join"] { hc := some "t2" }
  t.setHc [json% {"address": "t1"}]
  t.sw_ "f" ["task", "claim", "1"] { hc := some "t2" }
  t.q_ "update task set lease_until=?" [.int ((← now) - 60)]
  comms_tick t
  unless ← ended t "f" do fail "f not ended"
  eq (← taskState t) "ready"

def test_communicator_never_checked (t : T) : IO Unit := do
  idle t "comms" [("stay", "the user's channel"), ("last_active", .int ((← now) - 80 * 60))]
  comms_tick t
  eq (← evs t "stay-check") 0

-- spawn --stay: a stayer before its first turn, with --task (at reserve) and without
def test_spawn_stay (t : T) : IO Unit := do
  t.fakes
  t.sw_ "a" ["task", "add", "do it"]
  t.sw_ "a" ["spawn", "t-8", "--stay", "PRs to review", "--task", "1"]
  eq (← stay t "t-8") "PRs to review"
  t.sw_ "a" ["spawn", "t-9", "--stay", "the plan", "--", "go"]
  eq (← stay t "t-9") "the plan"

-- board #195: a stay with --until: set by the CLI, a backstop check at 50 min only, woken when the condition holds
def test_stay_until_cli (t : T) : IO Unit := do
  t.agent "e"
  has (← t.sw "e" ["stay", "x", "--until", "soon"] { ok := false }).stderr "bad --until"
  has (← t.sw "e" ["stay", "x", "--until", "time:25:00"] { ok := false }).stderr "bad --until"
  has (← t.sw "e" ["stay", "x", "--until", "task:#7"]).stdout "until task:7"
  eq ((← t.q1 "select path from event where kind='stay-until'").f "path") "task:7"
  t.sw_ "e" ["stay", "y"]  -- a plain stay after it is free-text again
  idle t "comms"
  t.q_ "update agent set status='idle', last_active=?, waiter=? where name='e'"
    [.int ((← now) - 16 * 60), .int (← IO.Process.getPID).toNat]
  t.q_ "update event set ts=? where kind in ('stay','stay-until')" [.int ((← now) - 16 * 60)]
  comms_tick t
  eq (← live t "e") 1
  t.sw_ "e" ["stay", "z", "--until", "ci"]
  t.q_ "update event set ts=? where kind in ('stay','stay-until')" [.int ((← now) - 16 * 60)]
  t.q_ "update agent set status='idle', last_active=? where name='e'" [.int ((← now) - 16 * 60)]
  comms_tick t
  eq (← live t "e") 1  -- a condition: no 15 min check
  t.q_ "delete from event where kind='stay-check'" []
  t.q_ "update agent set last_active=? where name='e'" [.int ((← now) - 51 * 60)]
  comms_tick t
  eq (← live t "e") 2  -- the backstop at 50

/-- Agent `s` stays with condition `cond` set an hour... 30 min ago; it claims #5 with a short lease. -/
def untilStay (t : T) (cond : String) : IO Unit := do
  idle t "comms"; idle t "s" [("stay", "the wait"), ("last_active", .int ((← now) - 60))]
  t.q_ "insert into event(ts, agent, kind, path, data) values (?, 's', 'stay-until', ?, 'the wait')" [.int ((← now) - 1800), .text cond]
  t.q_ "insert into task(id, title, state, owner, lease_until) values (5, 't', 'in_progress', 's', ?)" [.int ((← now) + 60)]
def woke (t : T) : IO Nat :=
  return (← t.q "select 1 x from msg where dest='s' and body like 'Your wait is over: %'").size
def wokeBody (t : T) : IO String :=
  return ((← t.q1 "select body from msg where dest='s' and body like 'Your wait is over: %'").f "body").s?.getD ""
def assertWoke (t : T) (cond detail : String) : IO Unit := do
  comms_tick t
  eq (← woke t) 1
  has (← wokeBody t) s!"Your wait is over: {cond} ({detail}"
  eq (← stay t "s") Json.null
  eq (← evs t "stay-wake") 1
  unless ((← t.q1 "select lease_until from task where id=5").f "lease_until").getInt?.toOption.getD 0 > (← now) + 7000 do
    fail "lease not renewed"
  comms_tick t
  eq (← woke t) 1  -- once
def assertWaiting (t : T) : IO Unit := do
  comms_tick t
  eq (← woke t) 0
  eq (← stay t "s") "the wait"

def test_until_job (t : T) : IO Unit := do
  untilStay t "job:j7"
  assertWaiting t
  t.q_ "insert into event(ts, agent, kind, path) values (?, 'x', 'job-end', 'j7')" [.int (← now)]
  assertWoke t "job:j7" "job j7 ended"

def test_until_task (t : T) : IO Unit := do
  untilStay t "task:9"
  t.q_ "insert into task(id, title, state) values (9, 'other', 'in_progress')"
  assertWaiting t
  t.q_ "update task set state='ready' where id=9"  -- open, but never released since the stay: still waiting
  assertWaiting t
  t.q_ "insert into event(ts, agent, kind, data) values (?, 'x', 'release', '#9 from x')" [.int (← now)]
  assertWoke t "task:9" "#9 was released"

def test_until_task_done (t : T) : IO Unit := do
  untilStay t "task:9"
  t.q_ "insert into task(id, title, state) values (9, 'other', 'in_progress')"
  assertWaiting t
  t.q_ "update task set state='completed' where id=9"
  assertWoke t "task:9" "#9 is Completed"

def test_until_msg (t : T) : IO Unit := do
  untilStay t "msg:p"
  idle t "q" [("stay", "x")]; idle t "p" [("stay", "x")]
  t.sw_ "q" ["post", "s", "not him"]
  assertWaiting t
  t.sw_ "p" ["post", "s", "hello"]
  assertWoke t "msg:p" "message #"

def test_until_ci (t : T) : IO Unit := do
  untilStay t "ci"
  t.q_ "insert into ci(id, sha, status, conclusion, updated, workflow) values (1, 'abcdef0123', 'completed', 'success', ?, 'ci')"
    [.text "2000-01-01T00:00:00Z"]
  assertWaiting t  -- a result from before the stay is not the next one
  t.q_ "insert into ci(id, sha, status, conclusion, updated, workflow) values (2, '0123456789', 'completed', 'failure', strftime('%Y-%m-%dT%H:%M:%SZ','now'), 'ci')" []
  assertWoke t "ci" "ci failure on 0123456"

def hhmm (e : Int) : String :=
  let m := (e % 86400) / 60
  s!"{m / 60}:{if m % 60 < 10 then "0" else ""}{m % 60}"
def test_until_time (t : T) : IO Unit := do
  untilStay t s!"time:{hhmm ((← now) + 600)}"
  assertWaiting t
  t.q_ "update event set path=? where kind='stay-until'" [.text s!"time:{hhmm ((← now) - 120)}"]
  assertWoke t s!"time:{hhmm ((← now) - 120)}" "it is past"

def tests : List Case := [
  ("test_stay_until_cli", test_stay_until_cli),
  ("test_until_job", test_until_job),
  ("test_until_task", test_until_task),
  ("test_until_task_done", test_until_task_done),
  ("test_until_msg", test_until_msg),
  ("test_until_ci", test_until_ci),
  ("test_until_time", test_until_time),
  ("test_stayer_not_ended_or_digested_until_end", test_stayer_not_ended_or_digested_until_end),
  ("test_stay_cut_and_empty_refused", test_stay_cut_and_empty_refused),
  ("test_stay_fenced_and_kept_by_takeover", test_stay_fenced_and_kept_by_takeover),
  ("test_reap_clears_stay", test_reap_clears_stay),
  ("test_stayers_expired_claim_reopens", test_stayers_expired_claim_reopens),
  ("test_stayer_done_line", test_stayer_done_line),
  ("test_quiet_notice_once_per_edge", test_quiet_notice_once_per_edge),
  ("test_quiet_cold_or_waiterless_stayer_not_woken", test_quiet_cold_or_waiterless_stayer_not_woken),
  ("test_hung_waiterless_reported_once", test_hung_waiterless_reported_once),
  ("test_hung_not_while_compacting", test_hung_not_while_compacting),
  ("test_hung_unread_message_reported_once", test_hung_unread_message_reported_once),
  ("test_hung_notice_not_reported", test_hung_notice_not_reported),
  ("test_liveness_check_hung_and_answered", test_liveness_check_hung_and_answered),
  ("test_compacting_holder_keeps_claim", test_compacting_holder_keeps_claim),
  ("test_compacting_unbound_owner_keeps_claim_until_continue", test_compacting_unbound_owner_keeps_claim_until_continue),
  ("test_cold_holder_woken_urgent", test_cold_holder_woken_urgent),
  ("test_live_idle_holder_keeps_claim_and_is_told", test_live_idle_holder_keeps_claim_and_is_told),
  ("test_hung_holder_claim_reopens", test_hung_holder_claim_reopens),
  ("test_ended_holder_claim_released", test_ended_holder_claim_released),
  ("test_communicator_never_checked", test_communicator_never_checked),
  ("test_spawn_stay", test_spawn_stay)]

end SwarmLean.Tests.Cli.Stay
