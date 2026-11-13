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
  return (← t.q "select 1 x from msg where dest=? and body like '%open task%'" [.text name]).size
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
  eq ((← t.q1 "select state from task").f "state") "open"
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
def to (t : T) (name : String) : IO (Array Json) :=
  t.q "select body from msg where dest=? and body not like '%no waiter%'" [.text name]
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
  idle t "s" [("stay", "the plan"), ("last_active", .int ((← now) - 49 * 60))]
  comms_tick t
  eq (← live t "s") 0  -- not before 50 minutes
  t.q_ "update agent set last_active=? where name='s'" [.int ((← now) - 51 * 60)]
  comms_tick t; comms_tick t
  eq (← live t "s") 1
  -- answered: last_active moved, no stay-hung; a new check goes out 50 idle minutes later
  t.q_ "update agent set last_active=? where name='s'" [.int (← now)]
  comms_tick t
  eq (← evs t "stay-hung") 0
  t.q_ "update event set ts=ts-7200 where kind='stay-check'"  -- the answer came long ago; idle again for 51 min
  t.q_ "update agent set last_active=? where name='s'" [.int ((← now) - 51 * 60)]
  comms_tick t
  eq (← live t "s") 2
  -- unanswered five minutes on: one urgent stay-hung, then no more checks
  t.q_ "update event set ts=ts-400 where kind='stay-check' and id=(select max(id) from event where kind='stay-check')"
  comms_tick t; comms_tick t
  eq (← evs t "stay-hung") 1
  eq (← t.q "select 1 x from msg where dest='comms' and urgent=1 and body like 's stays for%liveness check%swarm nudge s`%'").size 1
  eq (← live t "s") 2

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

def tests : List Case := [
  ("test_stayer_not_ended_or_digested_until_end", test_stayer_not_ended_or_digested_until_end),
  ("test_stay_cut_and_empty_refused", test_stay_cut_and_empty_refused),
  ("test_stay_fenced_and_kept_by_takeover", test_stay_fenced_and_kept_by_takeover),
  ("test_reap_clears_stay", test_reap_clears_stay),
  ("test_stayers_expired_claim_reopens", test_stayers_expired_claim_reopens),
  ("test_stayer_done_line", test_stayer_done_line),
  ("test_quiet_notice_once_per_edge", test_quiet_notice_once_per_edge),
  ("test_quiet_cold_or_waiterless_stayer_not_woken", test_quiet_cold_or_waiterless_stayer_not_woken),
  ("test_hung_waiterless_reported_once", test_hung_waiterless_reported_once),
  ("test_hung_unread_message_reported_once", test_hung_unread_message_reported_once),
  ("test_hung_notice_not_reported", test_hung_notice_not_reported),
  ("test_liveness_check_hung_and_answered", test_liveness_check_hung_and_answered),
  ("test_communicator_never_checked", test_communicator_never_checked),
  ("test_spawn_stay", test_spawn_stay)]

end SwarmLean.Tests.Cli.Stay
