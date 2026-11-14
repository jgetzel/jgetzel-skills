import Tests.Cli.Fixture

/-! cli_panel_spec.lua: the CLI the panel needs (REDESIGN.md §2, §3b): state --json's fate, ci and watchd; nudge;
stay --end for another agent; watchd --restart. -/

namespace SwarmLean.Tests.Cli.Panel
open SwarmLean.Tests.Cli
open Lean (Json toJson)
open SwarmLean.Sqlite (Val)

/-- Epoch seconds. -/
def now (t : T) : IO Int := do
  let r ← t.exec ["date", "+%s"]
  return (strip r.stdout).toInt!

abbrev Ch := IO.Process.Child { stdin := .null, stdout := .null, stderr := .null }

def myPid : IO Int := return Int.ofNat (← IO.Process.getPID).toNat

def idle (t : T) (name : String) (kw : List (String × Val) := []) : IO Unit := do
  let old := (← now t) - 3600
  let dflt : List (String × Val) := [("status", "idle"), ("last_active", .int old), ("waiter", .int (← myPid))]  -- a live waiter
  t.agent name (dflt.filter (fun (k, _) => !kw.any (·.1 == k)) ++ kw)

def commsTick (t : T) : IO Unit := t.sw_ "a" ["watchd", "--once", "--comms", "comms", "--max-agents", "0"]

def parse (s : String) : IO Json := match Json.parse s with
  | .ok j => pure j
  | .error e => fail s!"not JSON ({e}): {s}"

def st (t : T) (args : List String := []) : IO Json := do
  parse (← t.sw "a" (["state", "--json"] ++ args)).stdout

/-- The agent named `n` of a state. -/
def byName (s : Json) (n : String) : Json :=
  match s.f "agents" with
  | .arr a => (a.find? fun x => (x.f "name").s? == some n).getD .null
  | _ => .null

def nth (j : Json) (i : Nat) : Json := ((j.getArrVal? i).toOption).getD .null

def ended (t : T) (name : String) : IO Bool := do
  return (← t.q1 "select ended from agent where name=?" [.text name]).f "ended" != .null

-- fate is watchd's own verdict: what state --json says of each idle agent is what the next tick does to it
def test_fate_is_the_ticks_verdict (t : T) : IO Unit := do
  let uw := t.d ++ "/wu"
  discard <| t.git t.repo ["worktree", "add", "-q", "-b", "u1", uw]
  t.write "a" "../wu/new.txt" "scratch"  -- one uncommitted file
  idle t "comms"
  idle t "e" [("wt", t.wt)]                                     -- small, a ready task, a live waiter: reuse
  idle t "u" [("wt", uw)]                                       -- work not on its base: unclean
  idle t "s" [("wt", t.wt), ("stay", "reviews")]                -- kept by its stay
  idle t "z" [("wt", t.wt), ("waiter", .int 999999)]            -- small and a task ready, but no waiter: end
  idle t "w" [("wt", t.wt), ("status", "working")]              -- not idle: no fate
  t.sw_ "comms" ["task", "add", "t1"]
  let a ← st t ["--view", "agents"]
  let fate (n : String) := (byName a n).f "fate"
  eq (toJson [(fate "e").f "verdict", (fate "e").f "short", (fate "e").f "says"])
    (json% ["reuse", "#1 is ready", "Kept for reuse: #1 is ready"])
  eq (toJson [(fate "u").f "verdict", (fate "u").f "short"]) (json% ["unclean", "uncommitted work"])
  eq (toJson [(fate "s").f "verdict", (fate "s").f "short", (fate "s").f "says"])
    (json% ["kept", "stays", "Kept: stays"])
  eq (toJson [(fate "z").f "verdict", (fate "z").f "short"]) (json% ["end", "ending"])
  eq (fate "w") Json.null
  eq ((fate "u").f "checks").len 0  -- lanes: only the first reason
  -- every check for the one agent asked for, in the screen's order
  let u := (byName (← st t ["--view", "agents", "--agent", "u"]) "u").f "fate"
  let cs := match u.f "checks" with | .arr a => a | _ => #[]
  let labels := cs.map fun c => c.f "label"
  let lit := (cs.filter fun c => c.f "on" == Json.bool true).map fun c => c.f "label"
  eq labels (json% ["Stays", "Holds a task", "Holds a lock", "Work not on its base", "Background process",
    "Unread messages", "Terminal", "Waiter", "Idle", "Context"])
  eq lit (json% ["Work not on its base"])
  has ((nth (u.f "checks") 3).f "detail") "1 uncommitted file, 0 commits not on"
  has ((nth (u.f "checks") 8).f "detail") "watchd waits 2m"
  let e := (byName (← st t ["--agent", "e"]) "e").f "fate"
  for c in (match e.f "checks" with | .arr a => a | _ => #[]) do
    let l := (c.f "label").s?.getD ""
    eq (c.f "on") (Json.bool (l == "Context" || l == "Waiter")) l  -- reuse: the two that keep it together
  -- the tick does what fate said
  commsTick t
  eq (toJson [← ended t "e", ← ended t "u", ← ended t "s", ← ended t "z", ← ended t "w"])
    (json% [false, false, false, true, false])
  eq (← t.q "select 1 x from event where kind='digest' and agent='e'").size 1

-- a held task and lock: the first reason fate stops at, with every check shown on --agent
def test_fate_held_task_and_lock (t : T) : IO Unit := do
  idle t "e" [("wt", t.wt)]
  t.sw_ "e" ["task", "add", "t1"]; t.sw_ "e" ["task", "claim", "1"]; t.sw_ "e" ["lock", "b.txt"]
  t.q_ "update agent set status='idle', last_active=? where name='e'" [.int ((← now t) - 3600)]
  let f := (byName (← st t ["--view", "agents"]) "e").f "fate"
  eq (toJson [f.f "verdict", f.f "short"]) (json% ["kept", "holds #1"])
  let f := (byName (← st t ["--agent", "e"]) "e").f "fate"
  eq (f.f "says") "Kept: holds #1 and holds a lock"
  has ((nth (f.f "checks") 1).f "detail") "#1 t1, lease "
  eq ((nth (f.f "checks") 2).f "detail") "b.txt"

-- ci: the latest runs on the base and the red streak; watchd: its record, liveness and whether code is newer
def test_state_ci_and_watchd (t : T) : IO Unit := do
  t.sw_ "a" ["join"]
  let run (id : Int) (conc : Option String) (created : String) : IO Unit :=
    t.q_ "insert into ci(id,sha,status,conclusion,url,created) values(?,?,?,?,?,?)"
      [.int id, .text s!"s{id}", .text (if conc.isSome then "completed" else "in_progress"),
       (match conc with | some c => .text c | none => .null), .text s!"u{id}", .text created]
  run 1 (some "success") "2026-01-01T00:00:01Z"; run 2 (some "failure") "2026-01-01T00:00:02Z"
  run 3 (some "cancelled") "2026-01-01T00:00:03Z"; run 4 (some "failure") "2026-01-01T00:00:04Z"
  run 5 none "2026-01-01T00:00:05Z"
  let s ← st t
  eq ((s.f "ci").f "red_streak") 2
  let runs := (s.f "ci").f "runs"
  eq (toJson [(nth runs 0).f "id", (nth runs 0).f "status", (nth runs 1).f "conclusion", (nth runs 1).f "url"])
    (json% [5, "in_progress", "failure", "u4"])
  eq (s.f "watchd") Json.null
  let me ← myPid
  t.q_ "insert into meta(k,v) values('watchd',?)" [.text s!"{me} t3"]
  t.q_ "insert into meta(k,v) values('watchd_run',?)"
    [.text (json% {"flags": ["--comms", "c"], "cwd": $t.repo, "started": 1}).compress]
  let s ← st t
  let w := s.f "watchd"
  eq (toJson [w.f "pid", w.f "terminal", w.f "alive", w.f "stale", w.f "started", w.f "flags"])
    (json% [$me, "t3", true, true, 1, ["--comms", "c"]])
  t.q_ "update meta set v=? where k='watchd'" [.text "999999 -"]
  let later := (← now t) + 60
  t.q_ "update meta set v=? where k='watchd_run'"
    [.text (json% {"flags": [], "cwd": $t.repo, "started": $later}).compress]
  let s ← st t
  let w := s.f "watchd"
  eq (toJson [w.f "alive", w.f "stale", w.f "terminal"]) (json% [false, false, null])

-- nudge types the one line into a live agent's terminal and logs it; an ended agent is refused, nothing sent
def test_nudge (t : T) : IO Unit := do
  t.fakes
  t.sw_ "e" ["join"] { hc := some "t1" }
  t.sw_ "f" ["join"] { hc := some "t2" }
  t.sw_ "f" ["leave"] { hc := some "t2" }
  let out := (← t.sw "x" ["nudge", "e"] { env := [("SWARM_NAME", none)] }).stdout
  has out "nudged e (t1)"
  has (← t.calls "hc") "send t1 read your messages and continue, or say what you wait for"
  eq (← t.q1 "select agent,path from event where kind='nudge'") (json% {"agent": "human", "path": "e"})
  has (← t.sw "x" ["nudge", "f"] { ok := false }).stderr "f has ended"
  has (← t.sw "x" ["nudge", "nobody"] { ok := false }).stderr "nobody is not an agent"
  eq (← t.q "select 1 x from event where kind='nudge'").size 1
  -- nothing else moved: no message, no task, no stay
  eq (← t.q "select 1 x from msg").size 0

-- stay --end NAME: human and the communicator may; anyone else is refused; watchd then ends it by the normal rules
def test_stay_end_for_another (t : T) : IO Unit := do
  idle t "comms"
  t.q_ "insert or replace into meta(k,v) values('comms','comms')"
  idle t "e" [("wt", t.wt)]
  t.sw_ "e" ["stay", "reviews"]
  t.q_ "update agent set last_active=? where name='e'" [.int ((← now t) - 3600)]
  has (← t.sw "p" ["stay", "--end", "e"] { ok := false }).stderr "only human or the communicator"
  eq ((← t.q1 "select stay from agent where name='e'").f "stay") "reviews"
  commsTick t
  if ← ended t "e" then fail "a stayer was ended"
  has (← t.sw "x" ["stay", "--end", "e"] { env := [("SWARM_NAME", none)] }).stdout "e's stay ended"
  eq (← t.q1 "select agent,path,data from event where kind='stay-end'")
    (json% {"agent": "human", "path": "e", "data": "reviews"})
  has (← t.sw "comms" ["stay", "--end", "e"] { ok := false }).stderr "e stays for nothing"
  commsTick t
  unless ← ended t "e" do fail "no stay, landed and idle, yet not ended"
  has (← t.sw "comms" ["stay", "--end", "e"] { ok := false }).stderr "e is not a live agent"

-- ---- watchd --restart ----

/-- An hc whose `run` starts the command after `--` in the background (or run.script instead), unless run.none exists. -/
def restartHc (t : T) : IO Unit := do
  let D := shquote t.d
  discard <| t.fake "hc" ("#!/bin/sh\necho \"$*\" >> " ++ D ++ "/hc.log\ncase \"$1\" in\nls) exit 1 ;;\nrun)\n"
    ++ "  while [ \"$1\" != -- ]; do shift; done; shift\n"
    ++ "  [ -f " ++ D ++ "/run.none ] && { echo '{\"address\":\"t9\"}'; exit 0; }\n"
    ++ "  [ -f " ++ D ++ "/run.script ] && set -- sh " ++ D ++ "/run.script\n"
    ++ "  nohup \"$@\" > " ++ D ++ "/new.out 2>&1 < /dev/null &\n  echo $! > " ++ D ++ "/new.pid\n"
    ++ "  echo '{\"address\":\"t9\"}' ;;\n*) echo '{}' ;;\nesac\n")
  t.defer do
    if let some p ← slurp (t.d ++ "/new.pid") then
      if strip p != "" then discard <| t.exec ["kill", strip p]

/-- The first watchd, in the background, as `swarm watchd` started by hand: its handle and pid. -/
def firstWatchd (t : T) (args : List String) : IO (Ch × String) := do
  let pf := t.d ++ "/old.pid"
  let path := s!"{(← t.fakebin).getD ""}:{← basePath}"
  let script := "echo $$ > \"$1\"; shift; exec \"$@\" > " ++ shquote (t.d ++ "/old.err") ++ " 2>&1 < /dev/null"
  let argv := #["-c", script, "sh", pf, (← swarmBin), "watchd"] ++ args.toArray
  let env : Array (String × Option String) :=
    #[("SWARM_DB", some t.db), ("SWARM_NAME", some "comms"), ("HC_TERMINAL_ID", none), ("PATH", some path)]
  let c ← IO.Process.spawn { cmd := "sh", args := argv, cwd := some t.repo, env, stdin := .null, stdout := .null, stderr := .null }
  t.defer do
    discard <| t.exec ["kill", strip ((← slurp pf).getD "")]
    try discard c.wait catch _ => pure ()
  -- the pid is written by the shell that becomes swarm
  for _ in [0:100] do
    if strip ((← slurp pf).getD "") != "" then break
    IO.sleep 50
  return (c, strip ((← slurp pf).getD ""))

def mval (t : T) (k : String) : IO Json := do
  return (← t.q1 "select v from meta where k=?" [.text k]).f "v"

def until_ (what : String) (secs : Nat) (f : IO Bool) : IO Unit := do
  for _ in [0:secs * 10] do
    if ← f then return
    IO.sleep 100
  fail s!"timed out waiting for {what}"

def exited (c : Ch) : IO Bool := return (← c.tryWait).isSome

def test_watchd_restart_same_flags_old_exits (t : T) : IO Unit := do
  restartHc t
  t.sw_ "comms" ["join"]
  let (oc, old) ← firstWatchd t ["--interval", "1", "--comms", "comms", "--model", "haiku", "--max-agents", "2"]
  until_ "the first watchd's tick" 10 do return (← mval t "watchd_up") == Json.str s!"{old} -"
  let run ← parse (((← mval t "watchd_run").s?).getD "")
  eq (run.f "flags") (json% ["--interval", "1", "--min-free-mem", "4", "--comms", "comms", "--blocker-idle", "25", "--model", "haiku"])
  t.sw_ "a" ["limits", "--min", "5"]
  let r ← t.sw "x" ["watchd", "--restart"] { env := [("SWARM_NAME", none)] }
  has r.stdout "watchd restarted: pid "
  let new := strip ((← slurp (t.d ++ "/new.pid")).getD "")
  eq (← mval t "watchd") s!"{new} -"
  eq (← mval t "watchd_up") s!"{new} -"
  until_ "the old watchd to exit" 10 (exited oc)
  has ((← slurp (t.d ++ "/old.err")).getD "") s!"was replaced by {new}"
  let call := ((← t.calls "hc").filter (·.startsWith "run ")).getLast?.getD ""
  has call s!"run --json --bg --no-parent --no-notify --cwd {t.repo} -- "
  has call "watchd --takeover --interval 1 --min-free-mem 4 --comms comms --blocker-idle 25 --model haiku"
  eq (← mval t "agent_min") "5"  -- --max-agents is not replayed over the user's number
  eq (((← st t).f "watchd").f "pid") new.toNat!

-- flags given with --restart replace the recorded ones and add new ones
def test_watchd_restart_amends_flags (t : T) : IO Unit := do
  restartHc t
  t.sw_ "comms" ["join"]
  let (_, old) ← firstWatchd t ["--interval", "1", "--comms", "comms", "--model", "haiku"]
  until_ "the first watchd's tick" 10 do return (← mval t "watchd_up") == Json.str s!"{old} -"
  let r ← t.sw "x" ["watchd", "--restart", "--ci", "--model", "sonnet"] { env := [("SWARM_NAME", none)] }
  has r.stdout "watchd restarted: pid "
  let call := ((← t.calls "hc").filter (·.startsWith "run ")).getLast?.getD ""
  has call "watchd --takeover --interval 1 --min-free-mem 4 --comms comms --blocker-idle 25 --model sonnet --ci"

-- a new watchd that never shows up: refused, the old one keeps the record and runs on
def test_watchd_restart_nothing_started (t : T) : IO Unit := do
  restartHc t
  t.sw_ "comms" ["join"]
  let (oc, old) ← firstWatchd t ["--interval", "1", "--comms", "comms"]
  until_ "the first watchd's tick" 10 do return (← mval t "watchd_up") == Json.str s!"{old} -"
  t.write "a" "../run.none" ""
  let r ← t.sw "x" ["watchd", "--restart"] { ok := false, env := [("SWARM_NAME", none), ("SWARM_WATCHD_UP_WAIT", some "2")] }
  eq r.code 1
  has r.stderr s!"no new watchd took over within 2 s; the old watchd (pid {old}) still runs"
  eq (← mval t "watchd") s!"{old} -"
  if ← exited oc then fail "the old watchd exited"

-- one that takes the record and dies before its first tick: the record goes back and the old one runs on
def test_watchd_restart_new_dies (t : T) : IO Unit := do
  restartHc t
  t.sw_ "comms" ["join"]
  let (oc, old) ← firstWatchd t ["--interval", "1", "--comms", "comms"]
  until_ "the first watchd's tick" 10 do return (← mval t "watchd_up") == Json.str s!"{old} -"
  -- the Lua wrote die.lua (lsqlite3 update); the test binary's --sql does the same write
  put (t.d ++ "/run.script")
    s!"{shquote (← selfBin)} --sql {shquote t.db} \"update meta set v='999999 t9' where k='watchd'\"\n"
  let r ← t.sw "x" ["watchd", "--restart"] { ok := false, env := [("SWARM_NAME", none), ("SWARM_WATCHD_UP_WAIT", some "5")] }
  has r.stderr "watchd restart failed: the new watchd (999999 t9) died before its first tick; the old watchd"
  eq (← mval t "watchd") s!"{old} -"
  IO.sleep 2000
  if ← exited oc then fail "the old watchd exited"
  eq (← mval t "watchd") s!"{old} -"

-- the old watchd's side: replaced by a dead pid it takes the record back; by a live one that has not ticked, it waits
def test_watchd_hands_over_only_to_a_ticked_one (t : T) : IO Unit := do
  restartHc t
  t.sw_ "comms" ["join"]
  let (oc, old) ← firstWatchd t ["--interval", "1", "--comms", "comms"]
  until_ "the first watchd's tick" 10 do return (← mval t "watchd_up") == Json.str s!"{old} -"
  t.q_ "update meta set v='999999 t9' where k='watchd'"
  until_ "the record back" 10 do return (← mval t "watchd") == Json.str s!"{old} -"
  has (((← t.q1 "select data from event where kind='watchd-back'").f "data")) "999999 t9 died before its first tick"
  let me ← myPid
  t.q_ "update meta set v=? where k='watchd'" [.text s!"{me} t9"]  -- alive (this test), never ticked
  IO.sleep 2500
  if ← exited oc then fail "handed over to a watchd that never ticked"
  eq (← mval t "watchd") s!"{me} t9"
  t.q_ "update meta set v=? where k='watchd_up'" [.text s!"{me} t9"]
  until_ "the old watchd to exit" 10 (exited oc)

-- board #139: a view sends open work and live agents whole, done/dropped tasks and ended agents only where its screen
-- lists them, and `counts` of them all
def test_state_sends_what_the_view_lists (t : T) : IO Unit := do
  t.agent "e" [("ended", .int 1)]
  t.agent "w" [("status", "working")]
  t.q_ "insert into task(id, title, state, owner) values (1, 'one', 'done', 'w'), (2, 'two', 'done', 'x'), (3, 'three', 'dropped', null), (4, 'four', 'open', null)"
  t.q_ "update task set deps='1,2' where id=4"
  t.q_ "insert into event(ts, agent, kind, data) values (1, 'x', 'done', '#2 sha')"
  let ids (s : Json) : List Int := match s.f "tasks" with
    | .arr a => a.toList.filterMap fun k => (k.f "id").getInt?.toOption
    | _ => []
  let names (s : Json) : List String := match s.f "agents" with
    | .arr a => a.toList.filterMap fun x => (x.f "name").getStr?.toOption
    | _ => []
  let o ← st t ["--view", "overview"]  -- its event feed names #2
  eq (ids o) [2, 4]
  eq (o.f "counts") (json% {"open": 1, "claimed": 0, "blocked": 0, "done": 2, "dropped": 1, "ended": 1})
  eq ((nth (o.f "tasks") 1).f "undone") (json% [])
  if (names o).contains "e" then fail "overview sent an ended agent"
  eq (ids (← st t ["--view", "board"])) [1, 2, 3, 4]
  eq (ids (← st t ["--view", "agents", "--agent", "w"])) [1, 4]
  eq (ids (← st t ["--view", "agents", "--task", "4"])) [1, 2, 4]
  unless (names (← st t ["--view", "agents"])).contains "e" do fail "the agents view left out an ended agent"
  eq (ids (← st t)) [1, 2, 3, 4]

-- UI-SPEC.md slice 5: --view summary is task counts, the live agents in five fields and what needs the human
def test_state_summary (t : T) : IO Unit := do
  let n ← now t
  t.agent "comms" [("status", "idle"), ("last_active", .int (n - 100))]
  t.agent "w" [("status", "working"), ("last_active", .int n)]
  t.agent "p" [("status", "blocked")]                                         -- stopped at a prompt
  t.agent "q" [("status", "working"), ("last_active", .int 0)]               -- asks about #2; never active: idle 0
  t.agent "s" [("status", "idle"), ("stay", "reviews"), ("last_active", .int (n - 50))]  -- hung
  t.agent "e" [("ended", .int 1)]
  t.q_ "insert into task(id, title, state, owner, question) values (1, 'one', 'claimed', 'w', null), (2, 'two', 'blocked', 'q', 'which?'), (3, 'three', 'done', 'w', null), (4, 'four', 'open', null, null)"
  t.q_ "insert into event(ts, agent, kind, data) values (?, 's', 'stay-hung', ''), (?, 'w', 'claim', '#1')" [.int (n - 10), .int (n - 10)]
  t.q_ "insert into ci(id,sha,status,conclusion,url,created) values(7,'x','completed','failure','u','2026-11-08T10:00:00Z')"
  let s ← st t ["--view", "summary"]
  eq (s.f "counts") (json% {"open": 1, "claimed": 1, "blocked": 1, "done": 1, "dropped": 0})
  let ags := match s.f "agents" with | .arr a => a.toList | _ => []
  eq (ags.map (·.f "name")) [json% "comms", json% "p", json% "q", json% "s", json% "w"]
  eq (byName s "q") (json% {"name": "q", "status": "blocked", "task": {"id": 2, "title": "two"}, "idle_s": 0, "hung": false})
  eq ((byName s "w").f "task") (json% {"id": 1, "title": "one"})
  eq ((byName s "s").f "hung") (json% true)
  unless (((byName s "comms").f "idle_s").getInt?.toOption.getD 0) ≥ 100 do fail "comms' idle_s"
  let needs := match s.f "needs" with | .arr a => a.toList.filter fun (x : Json) => x.f "kind" != json% "memory" | _ => []
  eq (toJson needs) (json% [{"kind": "question", "task": 2, "agent": "q", "question": "which?", "title": "two"},
    {"kind": "prompt", "agent": "p"}, {"kind": "hung", "agent": "s"},
    {"kind": "ci", "run": 7, "url": "u", "created": "2026-11-08T10:00:00Z"}])
  for k in ["tasks", "events", "messages", "machine", "watchd"] do
    if s.f k != .null then fail s!"summary sent {k}"

def tests : List Case := [
  ("test_state_sends_what_the_view_lists", test_state_sends_what_the_view_lists),
  ("test_state_summary", test_state_summary),
  ("test_fate_is_the_ticks_verdict", test_fate_is_the_ticks_verdict),
  ("test_fate_held_task_and_lock", test_fate_held_task_and_lock),
  ("test_state_ci_and_watchd", test_state_ci_and_watchd),
  ("test_nudge", test_nudge),
  ("test_stay_end_for_another", test_stay_end_for_another),
  ("test_watchd_restart_same_flags_old_exits", test_watchd_restart_same_flags_old_exits),
  ("test_watchd_restart_amends_flags", test_watchd_restart_amends_flags),
  ("test_watchd_restart_nothing_started", test_watchd_restart_nothing_started),
  ("test_watchd_restart_new_dies", test_watchd_restart_new_dies),
  ("test_watchd_hands_over_only_to_a_ticked_one", test_watchd_hands_over_only_to_a_ticked_one)]

end SwarmLean.Tests.Cli.Panel
