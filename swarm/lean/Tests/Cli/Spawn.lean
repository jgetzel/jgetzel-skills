import Tests.Cli.Fixture
import SwarmLean.Lib.Cost
import SwarmLean.Real

/-! cli_spawn_spec.lua: auto-spawn, spawn, the cold-cache rule, waiters, `state --json`. -/

namespace SwarmLean.Tests.Cli.Spawn
open SwarmLean.Tests.Cli
open Lean (Json toJson)
open SwarmLean.Sqlite (Val)

/-- Runs an App action under the fixture's db. -/
def app (t : T) (act : App α) : IO α := do
  Shim.setenv "SWARM_DB" t.db
  match ← act.run.run { conn := ← IO.mkRef none } with
  | .ok a => return a
  | .error _ => fail "App action exited"

def touch (p : String) : IO Unit := put p ""
def sleep (s : Float) : IO Unit := IO.sleep (s * 1000).toUInt32
def ok (b : Bool) (msg : String) : IO Unit := unless b do fail msg
def now : IO Int := return (strip (← IO.Process.output { cmd := "date", args := #["+%s"] }).stdout).toInt!

/-- json.decode: null fields are absent. -/
partial def dropNulls : Json → Json
  | .obj kv => Json.mkObj (kv.toArray.toList.filterMap fun (k, v) => if v == .null then none else some (k, dropNulls v))
  | .arr a => .arr (a.map dropNulls)
  | j => j

/-- A Lua array's i-th element (1-based). -/
def nth (j : Json) (i : Nat) : Json := (j.getArrVal? (i - 1)).toOption.getD .null
def elems (j : Json) : List Json := ((j.getArr?).toOption.getD #[]).toList
def row (r : Json) (ks : List String) : Json := Json.arr (ks.map r.f).toArray
def kinds (j : Json) : Json := Json.arr ((elems j).map (·.f "kind")).toArray

def stj (t : T) (extra : List String := []) (env : List (String × Option String) := []) : IO Json := do
  let r ← t.sw "a" (["state", "--json"] ++ extra) { env }
  match Json.parse r.stdout with
  | .ok j => return dropNulls j
  | .error e => fail s!"state --json: {e}: {r.stdout}"

def argvOf (x : Json) : List String := (elems (x.f "argv")).map (·.s?.getD "")
def after (x : Json) (flag : String) : Option String :=
  let a := argvOf x
  ((a.zip a.tail).find? (·.1 == flag)).map (·.2)
def names (t : T) : IO (List String) := return (← t.launched).toList.map fun x => (argvOf x).headD ""

/-- A running `swarm <args>` as who (no HC_TERMINAL_ID), stderr to a file. -/
structure W where
  child : IO.Process.Child ⟨.null, .null, .null⟩
  errf : String

def bg (t : T) (who errname : String) (args : List String) : IO W := do
  let errf := t.d ++ "/" ++ errname
  let args := #["-c", "e=$1; shift; exec \"$@\" 2>\"$e\"", "sh", errf, (← swarmBin)] ++ args.toArray
  let env := #[("SWARM_DB", some t.db), ("SWARM_NAME", some who), ("HC_TERMINAL_ID", none)]
  let child ← IO.Process.spawn { cmd := "sh", args, env, stdin := .null, stdout := .null, stderr := .null }
  t.defer (do discard child.tryWait)
  return { child, errf }

/-- Exit code of a background job, failing if it outlives secs. -/
def reap (w : W) (secs : Nat) : IO Int := do
  for _ in [0:secs * 5] do
    if let some rc ← w.child.tryWait then return rc.toNat
    sleep 0.2
  fail s!"still running after {secs}s"

-- ---- auto-spawn ----
def tick (t : T) (cap : Nat) : IO Unit :=
  t.sw_ "a" ["watchd", "--once", "--comms", "t-comms", "--max-agents", toString cap, "--min-free-mem", "0"]

def twoHaiku (t : T) : IO Unit := do
  for n in ["t-comms", "t-1"] do t.agent n [("status", "working"), ("model", "haiku")]
  t.q_ "insert or replace into meta(k,v) values('comms','t-comms')"

def spawned (t : T) : IO (List (String × Option String)) :=
  return (← t.launched).toList.map fun x => ((argvOf x).headD "", after x "--model")

def test_auto_spawn_once_within_cap (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "a" ["task", "add", "do it"]
  tick t 1
  eq (← spawned t).length 0  -- at the cap
  tick t 2
  eq (← spawned t) [("t-2", some "sonnet")]  -- not the live agents' model
  eq ((← t.q1 "select owner,state from task").f "owner") "t-2"
  ok ((← t.q1 "select first_claimed_at f from task").f "f" != .null) "auto-spawn stamps the claim time"
  tick t 2
  eq (← spawned t).length 1  -- the task is claimed: no second spawn

def test_auto_spawn_model_order (t : T) : IO Unit := do
  t.fakes
  for n in ["t-comms", "t-1"] do t.agent n [("status", "working"), ("model", "opus")]
  t.sw_ "a" ["task", "add", "plain"]
  t.sw_ "a" ["task", "add", "own", "--model", "haiku"]
  tick t 3
  tick t 4
  let m := (← spawned t).filterMap (·.2)
  eq (m.toArray.qsort (· < ·)).toList ["haiku", "sonnet"]
  t.fakes
  t.sw_ "a" ["task", "add", "viaflag"]
  t.sw_ "a" ["watchd", "--once", "--comms", "t-comms", "--max-agents", "5", "--min-free-mem", "0", "--model", "opus"]
  eq ((← spawned t).getLast?.bind (·.2)) "opus"

def test_auto_spawn_failure_backs_off (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  touch (t.d ++ "/launch.fail")
  t.sw_ "a" ["task", "add", "do it"]
  tick t 2
  tick t 2  -- inside the backoff window: no second launch, no second notice
  eq (← names t) ["t-2"]
  let notes := (← t.q "select body from msg where dest='t-comms'").toList.filterMap fun r =>
    let b := (r.f "body").s?.getD ""
    if subIn b "auto-spawn" then some b else none
  eq notes.length 1
  has notes[0]! "no Herdr window"
  t.q_ "update meta set v='0,300,t-2' where k='spawn_backoff'"  -- window over
  tick t 2
  eq (← names t) ["t-2", "t-2"]  -- same name reused
  eq ((← t.q1 "select count(*) n from msg where body like '%auto-spawn%'").f "n") 1  -- still one notice

-- The name kept for the retry goes to the first task only; the next one this tick gets a fresh name.
def test_auto_spawn_backoff_name_used_once (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  touch (t.d ++ "/launch.fail")
  t.sw_ "a" ["task", "add", "one"]; t.sw_ "a" ["task", "add", "two"]
  tick t 4
  IO.FS.removeFile (t.d ++ "/launch.fail")
  t.q_ "update meta set v='0,300,t-2' where k='spawn_backoff'"  -- window over
  tick t 4
  eq (← names t) ["t-2", "t-2", "t-3"]
  eq ((← t.q1 "select count(*) n from meta where k in ('spawn_backoff','spawn_fails')").f "n") 0

def test_auto_spawn_gives_up_after_k_failures (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  touch (t.d ++ "/launch.fail")
  t.sw_ "a" ["task", "add", "do it"]
  for _ in [0:7] do
    tick t 2
    t.q_ "update meta set v='0,300,t-2' where k='spawn_backoff'"  -- window over
  eq (← t.launched).size 5  -- K=5, then no more launches
  let urgent ← t.q "select body from msg where dest='t-comms' and urgent=1 and body like '%in a row%'"
  eq urgent.size 1
  has (urgent[0]!.f "body") "no Herdr window"

-- ---- the user's staffing numbers (sw-roles §6) ----
def tick0 (t : T) : IO Unit := t.sw_ "a" ["watchd", "--once", "--comms", "t-comms", "--min-free-mem", "0"]

def test_limits_auto_spawn_number_read_each_tick (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  has (← t.sw "a" ["limits"]).stdout "agents: 1 live, no auto-spawn number, no max set"
  t.sw_ "a" ["limits", "--min", "1"]
  t.sw_ "a" ["task", "add", "one"]; t.sw_ "a" ["task", "add", "two"]
  tick0 t
  eq (← spawned t).length 0  -- 1 live, the number is 1: not past it
  has (← t.sw "a" ["board"]).stdout "auto-spawn holding: 1 live, the auto-spawn number is 1; 2 task(s) startable"
  tick0 t
  eq ((← t.q1 "select count(*) n from event where kind='spawn-held'").f "n") 1  -- one per edge
  t.sw_ "a" ["limits", "--min", "2"]  -- takes effect on the next tick, no restart
  tick0 t
  eq (← names t) ["t-2"]
  has (← t.sw "a" ["board"]).stdout "auto-spawn holding: 2 live, the auto-spawn number is 2; 1 task(s) startable"
  eq ((← t.q1 "select count(*) n from event where kind='spawn-held'").f "n") 1  -- still holding: no new edge
  t.sw_ "a" ["limits", "--min", "3"]; tick0 t
  eq (← names t) ["t-2", "t-3"]
  hasnt (← t.sw "a" ["board"]).stdout "auto-spawn holding"  -- nothing startable: the hold is over
  eq ((← t.q1 "select count(*) n from meta where k='spawn_held'").f "n") 0

def test_first_watchd_sets_the_number_to_the_live_count (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  tick0 t
  has (← t.sw "a" ["who"]).stdout "agents: 1 live, auto-spawn to 1, no max set"
  t.agent "t-5"; tick0 t  -- a later start keeps it
  has (← t.sw "a" ["board"]).stdout "agents: 2 live, auto-spawn to 1, no max set"

def test_spawn_refused_at_the_max (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "a" ["spawn", "t-8", "--", "go"]  -- no max set: nothing refused
  has (← t.sw "a" ["limits", "--max", "2"]).stdout "agents: 2 live, no auto-spawn number, max 2"
  let r ← t.sw "a" ["spawn", "t-9", "--", "go"] { ok := false }
  eq r.code 1
  has r.stderr "2 agents are live and the user's max is 2. The communicator can raise it"
  t.sw_ "a" ["task", "add", "do it"]
  has (← t.sw "a" ["spawn", "t-9", "--task", "1"] { ok := false }).stderr "the user's max is 2"
  eq (← t.launched).size 1  -- launched nothing
  ok ((← t.q1 "select 1 x from agent where name='t-9'") == .null) "a refused spawn leaves no row"
  eq ((← t.q1 "select state from task").f "state") "open"
  eq (← t.q "select 1 from event where kind='spawn-refused' and data='t-9'").size 2
  has (← t.sw "a" ["limits", "--min", "3"] { ok := false }).stderr "the auto-spawn number 3 is above the max 2"
  t.sw_ "a" ["limits", "--max", "3"]
  t.sw_ "a" ["spawn", "t-9", "--", "go"]  -- raising the max lets the next through
  eq (← names t) ["t-8", "t-9"]

def test_two_spawns_race_for_the_last_place (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "a" ["limits", "--max", "2"]
  let r ← t.exec ["sh", "-c", "\"$0\" spawn r-1 -- go >/dev/null 2>&1 & p=$!; \"$0\" spawn r-2 -- go >/dev/null 2>&1; b=$?; wait $p; echo $? $b",
    ← swarmBin] { env := [("SWARM_DB", some t.db), ("SWARM_NAME", some "a"), ("HC_TERMINAL_ID", none),
      ("PATH", some s!"{(← t.fakebin).getD ""}:{← basePath}"), ("SWARM_LAUNCH", some (← t.launch))], cwd := some t.repo }
  let codes := strip r.stdout
  ok (codes == "0 1" || codes == "1 0") s!"one wins: {codes}"
  eq (← t.launched).size 1
  eq ((← t.q1 "select count(*) n from agent where name like 'r-%'").f "n") 1

-- ---- spawn ----
def test_spawn_effort (t : T) : IO Unit := do
  t.fakes; twoHaiku t
  t.sw_ "a" ["spawn", "t-8", "--", "go"]
  eq (after (← t.launched)[0]! "--effort") Json.null  -- omitted: claude's own setting
  t.sw_ "a" ["spawn", "t-9", "--effort", "medium", "--", "go"]
  eq (after (← t.launched)[1]! "--effort") "medium"
  has (← t.sw "a" ["spawn", "t-7", "--effort", "huge", "--", "go"] { ok := false }).stderr "must be one of"
  t.sw_ "a" ["task", "add", "do it", "--effort", "low"]  -- auto-spawn carries the task's effort
  tick t 5
  eq (after (← t.launched)[2]! "--effort") "low"

def test_spawn_task_claims_before_launch (t : T) : IO Unit := do
  t.fakes
  t.sw_ "a" ["task", "add", "do it"]
  t.sw_ "a" ["spawn", "t-9", "--model", "haiku", "--task", "1"]
  has (← t.sw "a" ["spawn", "t-8", "--model", "haiku", "--", "go"]).stdout "machine:"  -- the note after the launch
  eq ((← t.launched)[0]!.f "task") (json% [["t-9", "claimed"]])  -- claimed by the new name before launch ran
  eq ((← t.q1 "select hc from agent where name='t-9'").f "hc") "hc1"
  has (← t.sw "a" ["spawn", "t-9", "--model", "haiku", "--task", "1"] { ok := false }).stderr "live agent"  -- a live name is refused

-- --base and spawn.base pick the start ref; a missing ref falls back to the landing base.
def test_spawn_base_ref (t : T) : IO Unit := do
  t.fakes
  discard <| t.git (some t.repo) ["branch", "green"]
  discard <| t.git (some t.repo) ["commit", "-q", "--allow-empty", "-m", "ahead"]  -- main moves past green
  let sha (r : String) : IO String := return strip ((← t.git (some t.repo) ["rev-parse", r]))
  for i in [1:5] do t.sw_ "a" ["task", "add", s!"t{i}"]
  t.sw_ "a" ["spawn", "s1", "--model", "haiku", "--task", "1", "--base", "green"]
  eq (← sha "s1/1") (← sha "green")
  IO.FS.createDirAll (t.repo ++ "/.claude")
  put (t.repo ++ "/.claude/swarm.json") "{\"spawn\": {\"base\": \"green\"}}"
  t.sw_ "a" ["spawn", "s2", "--model", "haiku", "--task", "2"]
  eq (← sha "s2/2") (← sha "green")
  t.sw_ "a" ["spawn", "s3", "--model", "haiku", "--task", "3", "--base", "nope"]
  eq (← sha "s3/3") (← sha "main")

-- The spawn message keeps the task line and body with the spawner's text after them, and ends with the repo's ci.flow line.
def test_spawn_message_task_body_text_and_ci_flow (t : T) : IO Unit := do
  t.fakes
  t.sw_ "a" ["task", "add", "do it", "--body", "done means X"]
  t.sw_ "a" ["spawn", "t-9", "--model", "haiku", "--task", "1", "--", "start with Y"]
  let mut brief := (argvOf (← t.launched)[0]!).getD 2 ""
  has brief "Board task #1: do it."; has brief "done means X\n\nstart with Y"
  has brief "`ci.flow` post-merge, or unset"  -- the new worktree has no .claude/swarm.json
  IO.FS.createDirAll (t.repo ++ "/.claude")
  put (t.repo ++ "/.claude/swarm.json") "{\"ci\": {\"flow\": \"pr-gated\"}}"
  t.sw_ "a" ["spawn", "t-8", "--model", "haiku", "--", "go"]
  brief := (argvOf (← t.launched)[1]!).getD 2 ""
  has brief "`ci.flow` pr-gated"; hasnt brief "Board task"

def test_spawned_agent_skips_older_broadcasts (t : T) : IO Unit := do
  t.fakes
  t.sw_ "a" ["task", "add", "do it"]
  t.sw_ "a" ["post", "@all", "old rule from another run"]
  t.sw_ "a" ["spawn", "t-9", "--model", "haiku", "--task", "1"]
  t.sw_ "a" ["post", "@all", "new rule"]
  let out := (← t.sw "t-9" ["read"] { hc := some "hc1" }).stdout
  hasnt out "old rule"; has out "new rule"

def test_spawn_launch_failure_keeps_live_agent (t : T) : IO Unit := do
  t.fakes; t.setHc [json% {"name": "t-9", "address": "t7"}]
  touch (t.d ++ "/launch.fail")
  t.sw_ "a" ["task", "add", "do it"]
  t.sw_ "a" ["spawn", "t-9", "--model", "haiku", "--task", "1"]
  eq (row (← t.q1 "select owner,state from task") ["owner", "state"]) (json% ["t-9", "claimed"])
  eq ((← t.q1 "select hc from agent where name='t-9'").f "hc") "t7"

def test_launch_sh_survives_failure_after_hc_run (t : T) : IO Unit := do
  let fb := t.d ++ "/lfb"
  IO.FS.createDirAll fb
  let j := (json% {"spaces": [{"id": "s", "tabs": [{"id": "b", "terminals": [{"terminal": "t1"}]}]}]}).compress
  put (fb ++ "/hc") "#!/bin/sh\necho '{\"address\": \"t5\"}'\n" "755"
  put (fb ++ "/herdr-app") ("#!/bin/sh\n[ \"$1\" = ls ] && echo '" ++ j ++ "' || exit 1\n") "755"
  let sh := (← swarmDir) ++ "/../relaunch/launch.sh"
  let r ← t.exec [sh, "x", "tab", "task"] { env := [("PATH", some s!"{fb}:{← basePath}"), ("HC_TERMINAL_ID", some "t1")] }
  eq (Json.arr #[toJson r.code, toJson ((splitlines (strip r.stdout)).getLast?.getD "")]) (json% [0, "t5"]) r.stderr

def test_spawn_task_launch_failure_rolls_back (t : T) : IO Unit := do
  t.fakes
  touch (t.d ++ "/launch.fail")
  t.sw_ "a" ["task", "add", "do it"]
  discard <| t.sw "a" ["spawn", "t-9", "--model", "haiku", "--task", "1"] { ok := false }
  eq (row (← t.q1 "select owner,state from task") ["owner", "state"]) (json% [null, "open"])
  ok ((← t.q1 "select ended from agent where name='t-9'").f "ended" != .null) "ended"

-- launch_agent raises before launch.sh runs (its settings file can't be written): the reservation is undone too
-- (model Spawn.lean, Sp1: finding #28)
def test_spawn_task_raise_rolls_back (t : T) : IO Unit := do
  t.fakes
  IO.FS.createDirAll (t.d ++ "/agents/t-9.settings.json")
  t.sw_ "a" ["task", "add", "do it"]
  discard <| t.sw "a" ["spawn", "t-9", "--model", "haiku", "--task", "1"] { ok := false }
  eq (row (← t.q1 "select owner,state from task") ["owner", "state"]) (json% [null, "open"])
  ok ((← t.q1 "select ended from agent where name='t-9'").f "ended" != .null) "ended"
  eq (← t.launched).size 0

def test_agent_without_terminal_reads_as_gone (t : T) : IO Unit := do
  t.fakes; t.setHc [json% {"address": "t1"}]  -- only t1 is live
  t.agent "a"; t.agent "alive"; t.agent "x-comms" [("status", "idle")]; t.agent "w" [("status", "idle")]
  t.q_ "update agent set hc='t1' where name='alive'"
  t.q_ "update agent set hc='dead' where name in ('x-comms','w')"
  let who := (← t.sw "a" ["who"]).stdout
  has who "x-comms gone: no terminal; swarm join --takeover x-comms"
  hasnt who "x-comms idle"
  has who "alive idle"
  t.sw_ "a" ["spawn", "t-9", "--model", "haiku", "--", "go"]
  let brief := (argvOf (← t.launched)[0]!).getD 2 ""
  has brief "alive (idle)"; hasnt brief "x-comms"; hasnt brief "w ("
  let out := (← t.sw "a" ["post", "x-comms", "hi"]).stdout
  has out "can't be delivered now"; has out "stored"
  hasnt out "held;"; hasnt out "nudge by SendMessage"
  has (← t.sw "a" ["post", "@all", "hi"]).stdout "w, x-comms: no terminal"

def test_spawn_role_set_before_and_shown_in_roster (t : T) : IO Unit := do
  t.fakes
  t.sw_ "a" ["join"]; t.sw_ "a" ["role", "orchestrator"]
  t.sw_ "a" ["task", "add", "do it"]
  t.sw_ "a" ["spawn", "t-9", "--model", "haiku", "--role", "reviewer", "--task", "1"]
  eq ((← t.q1 "select role from agent where name='t-9'").f "role") "reviewer"
  t.sw_ "a" ["spawn", "t-8", "--model", "haiku", "--role", "planner", "--", "go"]
  eq ((← t.q1 "select role from agent where name='t-8'").f "role") "planner"
  has ((argvOf (← t.launched)[1]!).getD 2 "") "a (idle, orchestrator)"
  eq ((← t.q1 "select count(*) n from event where kind='role' and agent='t-9' and data='reviewer'").f "n") 1

def test_rules_appended_to_spawn (t : T) : IO Unit := do
  t.fakes
  eq (strip (← t.sw "a" ["rules", "set", "never", "edit", "main"]).stdout) "never edit main"
  t.sw_ "a" ["spawn", "t-9", "--model", "haiku", "--", "go"]
  has ((argvOf (← t.launched)[0]!).getD 2 "") "never edit main"

-- ---- cold-cache rule ----
def sendmsg (t : T) (to : String) (text : String := "hi") : IO Json :=
  t.hook "a" "pre-tool" (json% {"tool_name": "SendMessage", "tool_input": {"to": $to, "message": $text}})

def cache (extra : List (String × Val)) : List (String × Val) :=
  let base : List (String × Val) := [("status", "idle"), ("ctx_tokens", 140000), ("compacted_at", 0)]
  base.filter (fun (k, _) => (extra.lookup k).isNone) ++ extra

def test_cold_cache_cheap_cases_and_cold (t : T) : IO Unit := do
  t.agent "a"
  let now ← now
  let cold := cache [("last_active", .int (now - 72 * 60))]
  let with_ (k : String) (v : Val) : List (String × Val) := cold.filter (·.1 ≠ k) ++ [(k, v)]
  let cheap : List (String × List (String × Val)) := [("working", with_ "status" "working"),
    ("warm", with_ "last_active" (.int (now - 10 * 60))), ("compacted", with_ "compacted_at" (.int (now - 60))),
    ("small", with_ "ctx_tokens" 30000)]
  for (n, kw) in cheap do
    t.agent n kw
    eq (← sendmsg t n) (json% {}) n
  t.agent "cold" cold
  let out ← sendmsg t "cold"
  eq (out.f "permissionDecision") "deny"
  has (out.f "permissionDecisionReason") "idle 72 min"
  has (out.f "permissionDecisionReason") "140k"
  eq ((← t.q1 "select path from event where kind='deny-cold'").f "path") "cold"
  eq (← sendmsg t "nobody-we-know") (json% {})  -- not a member
  has (← t.sw "a" ["post", "cold", "later"]).stdout "held, cold"  -- stored without a wake
  eq (← t.sw "cold" ["wait", "--timeout", "2", "--poll", "0.2"] { ok := false }).code 0  -- non-urgent stays held

/-- A line holding `pre` and, later on it, `post` (Lua `pre [^\n]*post`). -/
def seqIn (s pre post : String) : Bool := (splitlines s).any fun l =>
  match l.splitOn pre with
  | _ :: rest@(_ :: _) => subIn (pre.intercalate rest) post
  | _ => false

def test_session_turns_keep_cache_warm (t : T) : IO Unit := do
  t.agent "a"
  let now ← now
  discard <| t.fake "hc" ("#!/bin/sh\necho '{\"status_ms\": " ++ toString ((now - 60) * 1000) ++ "}'\n")
  let kw : List (String × Val) := [("status", "idle"), ("ctx_tokens", 140000), ("last_active", .int (now - 4 * 3600)),
    ("compacted_at", 0)]
  t.agent "comms" kw; t.q_ "update agent set hc='t1' where name='comms'"
  t.agent "nohc" kw
  eq (← sendmsg t "comms") (json% {})
  eq ((← sendmsg t "nohc").f "permissionDecision") "deny"
  let who := (← t.sw "a" ["who"]).stdout
  ok (seqIn who "comms idle " "idle=1m cache=warm" && !seqIn who "comms idle " "cache=warm COLD") who
  ok (seqIn who "nohc idle " "cache=cold COLD-GUARDED") who

def test_wait_fenced_join_rebinds_dead_hc (t : T) : IO Unit := do
  t.agent "a"
  let now ← now
  discard <| t.fake "hc" ("#!/bin/sh\n[ \"$1\" = ls ] && echo '{\"terminals\": []}' && exit; [ \"$2\" = new ] && echo '{\"status_ms\": "
    ++ toString ((now - 60) * 1000) ++ "}' || echo '{}'\n")
  t.agent "comms" [("hc", "dead"), ("status", "idle"), ("ctx_tokens", 140000), ("last_active", .int (now - 4 * 3600)),
    ("compacted_at", 0)]
  t.sw_ "a" ["post", "comms", "later"]
  eq (← t.sw "comms" ["wait", "--timeout", "2", "--poll", "0.2"] { ok := false }).code 3  -- outside Herdr while bound to "dead": fenced
  eq (← t.sw "comms" ["wait", "--timeout", "1"] { ok := false, hc := some "new" }).code 3  -- fenced: no rebind
  eq ((← t.q1 "select hc from agent where name='comms'").f "hc") "dead"
  t.sw_ "comms" ["join"] { hc := some "new" }  -- hc ls doesn't show dead live: join moves it without --takeover
  let w ← t.sw "comms" ["wait", "--timeout", "3", "--poll", "0.2"] { ok := false, hc := some "new" }
  eq w.code 2
  has w.stderr "later"
  eq ((← t.q1 "select hc from agent where name='comms'").f "hc") "new"

def test_urgent_override (t : T) : IO Unit := do
  t.agent "a"
  t.agent "cold" [("status", "idle"), ("ctx_tokens", 140000), ("last_active", .int ((← now) - 4000)), ("compacted_at", 0)]
  eq (← sendmsg t "cold" "[urgent] main is red") (json% {})
  t.sw_ "a" ["post", "cold", "--urgent", "stop pushing"]
  let w ← t.sw "cold" ["wait", "--timeout", "3", "--poll", "0.2"] { ok := false }
  eq w.code 2
  has w.stderr "stop pushing"
  eq ((← t.q1 "select data from event where kind='wake'").f "data") "1 msg urgent"

def test_wait_wakes_warm_idle (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "a" ["post", "b", "ping"]
  let w ← t.sw "b" ["wait", "--timeout", "3", "--poll", "0.2"] { ok := false }
  eq w.code 2
  has w.stderr "ping"

def test_prompt_hook_delivers_and_stops_waiter (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  let w ← bg t "b" "w.err" ["wait", "--timeout", "10", "--poll", "0.2"]
  sleep 1
  eq (← t.hook "b" "prompt" (json% {"prompt": "hi"})) (json% {})  -- turn without a tool call: status -> working
  eq (← reap w 5) 0  -- old waiter exits; no double delivery
  t.sw_ "a" ["post", "b", "while idle"]
  has ((← t.hook "b" "prompt" (json% {"prompt": "x"})).f "additionalContext") "while idle"
  has (← t.sw "b" ["read"]).stdout "no unread"

def test_newest_waiter_owns_inbox (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  let w1 ← bg t "b" "w1.err" ["wait", "--timeout", "10", "--poll", "0.2"]
  sleep 0.8
  let w2 ← bg t "b" "w2.err" ["wait", "--timeout", "10", "--poll", "0.2"]
  sleep 0.8
  eq (← reap w1 5) 0  -- superseded without ever seeing 'working'
  has (← t.sw "a" ["post", "b", "ping"]).stdout "wakes"
  eq (← reap w2 5) 2
  has ((← slurp w2.errf).getD "") "ping"
  has (← t.sw "a" ["post", "b", "again"]).stdout "no live waiter"

def test_post_to_comms_has_no_sendmessage_nudge (t : T) : IO Unit := do
  t.agent "a"; t.agent "x-comms" [("status", "idle"), ("last_active", .int (← now))]
  t.q_ "insert or replace into meta(k,v) values('comms','x-comms')"
  let out := (← t.sw "a" ["post", "x-comms", "hi"]).stdout
  hasnt out "nudge by SendMessage"
  has out "held"
  t.agent "b" [("status", "idle"), ("last_active", .int (← now))]
  has (← t.sw "a" ["post", "b", "hi"]).stdout "nudge by SendMessage"

def test_sendmessage_ref_and_hookless_waiter (t : T) : IO Unit := do
  t.agent "a"
  t.agent "cold" [("status", "idle"), ("ctx_tokens", 140000), ("last_active", .int ((← now) - 4000)), ("compacted_at", 0)]
  eq ((← sendmsg t "cold [ab12]").f "permissionDecision") "deny"
  t.sw_ "c" ["join"]  -- no hooks: idle, ctx 0 counts as cheap
  t.sw_ "a" ["post", "c", "inbox"]
  let w ← t.sw "c" ["wait", "--timeout", "3", "--poll", "0.2"] { ok := false }
  eq w.code 2
  has w.stderr "inbox"

def test_stop_hook_records_ctx (t : T) : IO Unit := do
  t.agent "a"
  let tr := t.d ++ "/t.jsonl"
  put tr ((json% {"type": "assistant", "message": {"usage": {"input_tokens": 10, "cache_read_input_tokens": 90000,
    "cache_creation_input_tokens": 500}}}).compress ++ "\n")
  discard <| t.hook "a" "stop" (json% {"transcript_path": $tr})
  eq (row (← t.q1 "select status,ctx_tokens from agent where name='a'") ["status", "ctx_tokens"]) (json% ["idle", 90510])
  discard <| t.hook "a" "session" (json% {"source": "compact", "transcript_path": $tr})
  ok (((← t.q1 "select compacted_at c from agent where name='a'").f "c").i > 0) "compacted_at"

-- ---- board / state ----
def test_board_who (t : T) : IO Unit := do
  t.agent "a"
  t.sw_ "a" ["task", "add", "do it"]
  has (← t.sw "a" ["board"]).stdout "do it"
  has (← t.sw "a" ["who"]).stdout "a idle"

def test_state_json (t : T) : IO Unit := do
  eq ((← stj t).f "active") false
  ok (!(← (t.db : System.FilePath).pathExists)) "read-only: no db is created"
  t.agent "a" [("model", "opus"), ("ctx_tokens", 90000)]
  t.agent "b"
  t.sw_ "a" ["task", "add", "first"]
  t.sw_ "a" ["task", "add", "second", "--after", "1"]
  t.sw_ "a" ["task", "claim", "1"]
  t.sw_ "a" ["task", "block", "1", "which db?"]
  t.sw_ "b" ["lock", "b.txt"]
  t.sw_ "a" ["post", "b", "hello"]
  t.sw_ "b" ["leave"]
  let before := (← t.q1 "select count(*) n from event").f "n"
  let s ← stj t
  eq ((← t.q1 "select count(*) n from event").f "n") before
  ok (s.f "active" == Json.bool true) "active"
  let t1 := nth (s.f "tasks") 1; let t2 := nth (s.f "tasks") 2
  eq (row t1 ["state", "owner", "question"]) (json% ["blocked", "a", "which db?"])
  ok ((t1.f "lease_left").i > 0) "lease_left"
  ok (t2.f "waiting" == Json.bool true) "waiting"
  let a := nth (s.f "agents") 1; let b := nth (s.f "agents") 2
  eq (row a ["name", "status", "model", "ctx_tokens", "cache"]) (json% ["a", "blocked", "opus", 90000, "warm"])
  eq ((a.f "task").f "id") 1
  eq ((nth (a.f "messages") 1).f "body") "hello"
  eq (row b ["name", "status"]) (json% ["b", "ended"])
  eq ((nth (s.f "messages") 1).f "dest") "b"
  has (kinds (s.f "events")) "block"
  ok (s.f "machine" != .null) "machine"
  t.sw_ "a" ["post", "b", "".pushn 'x' 5000]
  eq (((nth ((← stj t).f "messages") 1).f "body").s?.getD "").length 500  -- long bodies (briefs) are cut

def test_state_json_round2 (t : T) : IO Unit := do
  t.agent "a"
  t.q_ "update agent set status='idle', last_active=1000 where name='a'"
  t.q_ "update agent set wt=? where name='a'" [.text t.repo]
  let repo := t.repo
  discard <| t.hook "a" "post-tool" (json% {"tool_name": "Bash", "tool_input": {"command": "git push"}, "cwd": $repo})
  t.q_ "update agent set status='idle', last_active=1000 where name='a'"
  t.q_ "insert or replace into event(ts,agent,kind,data) values(1,'a','push','git push old')"
  t.q_ "insert or replace into meta(k,v) values('comms','sr-comms')"
  let s ← stj t
  let a := nth (s.f "agents") 1
  eq (Json.arr #[s.f "comms", a.f "branch", a.f "cold_at"]) (json% ["sr-comms", "main", 4300])
  let mut pushes := (elems (s.f "events")).filter (·.f "kind" == Json.str "push")
  eq (row pushes[0]! ["branch", "subject"]) (json% [null, null])  -- older event
  eq (row pushes[1]! ["branch", "subject"]) (json% ["main", "init"])
  discard <| t.git (some t.wt) ["commit", "-q", "--allow-empty", "-m", "wt work"]
  for cmd in [s!"cd {t.wt} && git push", s!"git -C '{t.wt}' push", "cd ../wt; git push -u origin w2"] do
    discard <| t.hook "a" "post-tool" (json% {"tool_name": "Bash", "tool_input": {"command": $cmd}, "cwd": $repo})
  pushes := ((elems ((← stj t).f "events")).filter (·.f "kind" == Json.str "push")).take 3  -- newest first
  eq (Json.arr (pushes.map (row · ["branch", "subject"])).toArray) (json% [["w2", "wt work"], ["w2", "wt work"], ["w2", "wt work"]])  -- the worktree's

def keysOf (j : Json) : List String :=
  (((j.getObj?.toOption.map (·.toArray.toList.map (·.1))).getD []).toArray.qsort (· < ·)).toList

def test_state_json_view (t : T) : IO Unit := do
  t.agent "a" [("wt", t.wt)]
  t.agent "b"
  t.sw_ "a" ["task", "add", "t"]
  t.sw_ "b" ["lock", "b.txt"]
  t.sw_ "a" ["post", "b", "hi"]
  t.sw_ "b" ["leave"]
  let head := ["active", "db", "now", "comms", "tasks", "agents", "conflicts", "pressure", "machine", "limits", "ci", "counts"]
  -- "view" and "comms" are null in JSON where unset (decoded as absent), so compare what exists
  let views : List (String × List String) := [("board", []), ("activity", ["messages", "events"]),
    ("system", ["events", "locks", "running", "costly", "cost_top"]), ("overview", ["messages", "events"]), ("agents", [])]
  for (view, extra) in views do
    let s ← stj t ["--view", view]
    let want := (head ++ extra ++ ["view"]).filter fun k => !((k == "comms" || k == "db") && s.f k == .null)
    eq (keysOf s) (want.toArray.qsort (· < ·)).toList view
    let a := nth (s.f "agents") 1; let b := nth (s.f "agents") 2
    eq (a.f "messages") Json.null  -- per-agent messages only for --agent
    eq (a.f "events" != .null) (view == "overview" || view == "agents" || view == "system") view  -- live lanes
    eq (b.f "events") Json.null  -- ended and not asked for
  eq ((nth ((← stj t ["--view", "board"]).f "tasks") 1).f "title") "t"
  let ag := (← stj t ["--view", "agents", "--agent", "b"]).f "agents"
  let a := nth ag 1; let b := nth ag 2
  eq (Json.arr #[(nth (b.f "messages") 1).f "body", a.f "branch"]) (json% ["hi", "w2"])  -- w2: read from the worktree's HEAD
  has (kinds (b.f "events")) "leave"
  let full ← stj t
  eq (full.f "view") Json.null
  ok ((nth (full.f "agents") 2).f "locks" != .null) "no --view: everything, as before"
  for i in [0:80] do t.q_ s!"insert into event(ts,agent,kind,data) values({i},'a','claim','#{i}')"
  ok ((elems ((← stj t ["--view", "activity"]).f "events")).length > 80) "Activity reads further back"
  eq (elems ((← stj t ["--view", "overview"]).f "events")).length 60

-- ---- fake /proc ----
def fakeProc (t : T) (availKb : Nat := 20000000) (psi : String := "1.0") : IO String := do
  let r := t.d ++ "/proc"
  IO.FS.createDirAll (r ++ "/pressure")
  put (r ++ "/uptime") "10000.0 0\n"
  put (r ++ "/meminfo") s!"MemTotal: 32000000 kB\nMemAvailable: {availKb} kB\n"
  for k in ["memory", "cpu"] do put (r ++ "/pressure/" ++ k) s!"some avg10={psi} avg60=0 avg300=0 total=0\n"
  discard <| t.fake "ps" "#!/bin/sh\ncat \"$SWARM_PROC\"/[0-9]*/ps 2>/dev/null; exit 0\n"  -- machine.procs() reads the fixture
  return r

def addProc (t : T) (r : String) (pid ppid : Nat) (comm : String) (argv : List String) (rssPages : Nat := 0)
    (ageS : Nat := 240) : IO Unit := do
  let d := r ++ "/" ++ toString pid
  IO.FS.createDirAll d
  let tck := (strip (← t.exec ["getconf", "CLK_TCK"]).stdout).toNat!
  let f := ["S", toString ppid] ++ List.replicate 17 "0" ++ [toString ((10000 - ageS) * tck), "0", toString rssPages]
  put (d ++ "/stat") (s!"{pid} ({comm}) " ++ " ".intercalate f)
  put (d ++ "/cmdline") ("\x00".intercalate argv ++ "\x00")
  put (d ++ "/oom_score_adj") "0"
  let sec := ageS % 60
  put (d ++ "/ps") s!"{pid} {ppid} {rssPages * 4} {ageS / 60}:{if sec < 10 then "0" else ""}{sec} 0:00 {" ".intercalate argv}\n"

def test_state_json_running (t : T) : IO Unit := do
  let pr ← fakeProc t
  discard <| t.hook "a" "session"
  t.q_ "update agent set claude_pid=100 where name='a'"
  addProc t pr 100 1 "claude" ["claude"]
  addProc t pr 102 100 "cabal" ["/x/bin/cabal", "build"] 250000 125
  addProc t pr 150 1 "claude" ["claude"]
  addProc t pr 200 150 "node" ["node", "/x/bin/tsc", "-b"] 125000
  let st (extra : List String) := stj t extra [("SWARM_PROC", some pr)]
  let got := (elems ((← st ["--view", "system"]).f "running")).map
    (row · ["agent", "command", "elapsed_s", "rss_kb", "top_kb"])
  eq got (json% [["a", "cabal build", 125, 1000000, 1000000], ["other session", "tsc -b", 240, 500000, 500000]])
  eq ((← st ["--view", "board"]).f "running") Json.null

-- what the panel shows of sw-roles: the staffing numbers, the holding line, a stayer's hung sign, the cost history
def test_state_json_staffing (t : T) : IO Unit := do
  t.agent "a"
  t.agent "b" [("status", "idle"), ("stay", "reviews"), ("last_active", 1000)]
  t.agent "cm"
  t.q_ "insert or replace into meta(k,v) values('comms','cm')"
  eq ((← stj t ["--view", "board"]).f "limits") (json% {"live": 2, "queue_only": false})  -- the communicator is not counted; unset numbers are null
  t.sw_ "cm" ["limits", "--min", "2", "--max", "3"]
  t.q_ "insert into meta(k,v) values('spawn_held','auto-spawn holding: 2 live, the auto-spawn number is 2; 1 task(s) startable; max 3')"
  t.q_ "insert into event(ts,agent,kind) values(900,'b','stay-hung')"  -- before it was last active: over
  t.q_ "insert into event(ts,agent,kind) values(1100,'b','stay-unwoken')"
  let mut s ← stj t ["--view", "board"]
  eq (row (s.f "limits") ["live", "min", "max"]) (json% [2, 2, 3])
  has ((s.f "limits").f "held") "auto-spawn holding"
  let sign (s : Json) := Json.mkObj ((elems (s.f "agents")).filterMap fun x =>
    if x.f "stay_sign" == .null then none else some ((x.f "name").s?.getD "", x.f "stay_sign"))
  eq (sign s) (json% {"b": "unwoken"})
  t.q_ "insert into event(ts,agent,kind) values(1200,'b','stay-hung')"
  eq ((nth ((← stj t ["--view", "board"]).f "agents") 2).f "stay_sign") "hung"
  let host ← Shim.hostname
  let repo : Option String ← app t (SwarmLean.Cost.repoName (m := App) (some t.repo))
  let ts ← now
  for (rp, cmd, kb) in [(repo.getD "", "cargo test -p x", 9000000), (repo.getD "", "cargo test -p y", 5000000),
      (repo.getD "", "make", 7000000), ("elsewhere", "bazel build", 99000000)] do
    discard <| app t (SwarmLean.Cost.record (m := App) { ts, machine := host, repo := rp, agent := "a", cmd, wall_s := 90, peak_kb := kb })
  s ← stj t ["--view", "system"]
  let top := (elems (s.f "cost_top")).map (row · ["key", "n", "peak_kb"])
  eq top (json% [["cargo test -p", 2, 9000000], ["make", 1, 7000000]])  -- this repo only, by peak
  eq (elems (s.f "costly")).length 3

def test_state_json_hc_only_where_shown (t : T) : IO Unit := do
  let now ← now
  let log := t.d ++ "/hc.log"
  discard <| t.fake "hc" ("#!/bin/sh\necho \"$2\" >> " ++ log ++ "\necho '{}'\n")
  t.agent "live" [("hc", "t-live"), ("status", "idle"), ("last_active", .int (now - 4 * 3600))]
  t.agent "gone" [("hc", "t-gone"), ("status", "idle"), ("last_active", .int (now - 4 * 3600))]
  t.q_ "update agent set ended=? where name='gone'" [.int now]
  let hcCalls : IO (List String) := return match ← slurp log with | some s => splitlines s | none => []
  t.sw_ "a" ["state", "--json", "--view", "board"]
  eq (← hcCalls).length 0  -- board shows no idle timers
  t.sw_ "a" ["state", "--json"]
  eq (← hcCalls) ["t-live", "--json"]  -- never an ended agent's terminal; one `hc ls --json` for the live one's fate

def test_state_json_old_db (t : T) : IO Unit := do
  let c ← SwarmLean.Sqlite.Conn.open t.db false  -- schema from before agent.wt / task.after,model,question
  c.script "create table agent(name text primary key, hc text, model text, cwd text, status text, last_active int,
 ctx_tokens int default 0, compacted_at int default 0, started int, ended int, snap text, waiter int);
create table task(id integer primary key, title text, body text, state text, owner text, lease_until int,
 created_by text, evidence text);
create table msg(id integer primary key, ts int, frm text, dest text, body text, urgent int, kind text);
create table event(id integer primary key, ts int, agent text, kind text, path text, data text);
insert into agent(name,status,last_active) values('a','idle',1);
insert into task(title,state) values('t','open');"
  let s ← stj t
  ok (s.f "active" == Json.bool true) "active"
  eq (Json.arr #[(nth (s.f "agents") 1).f "worktree", (nth (s.f "tasks") 1).f "waiting"]) (json% [null, false])

def tests : List Case := [
  ("test_auto_spawn_once_within_cap", test_auto_spawn_once_within_cap),
  ("test_auto_spawn_model_order", test_auto_spawn_model_order),
  ("test_auto_spawn_failure_backs_off", test_auto_spawn_failure_backs_off),
  ("test_auto_spawn_backoff_name_used_once", test_auto_spawn_backoff_name_used_once),
  ("test_auto_spawn_gives_up_after_k_failures", test_auto_spawn_gives_up_after_k_failures),
  ("test_limits_auto_spawn_number_read_each_tick", test_limits_auto_spawn_number_read_each_tick),
  ("test_first_watchd_sets_the_number_to_the_live_count", test_first_watchd_sets_the_number_to_the_live_count),
  ("test_spawn_refused_at_the_max", test_spawn_refused_at_the_max),
  ("test_two_spawns_race_for_the_last_place", test_two_spawns_race_for_the_last_place),
  ("test_spawn_effort", test_spawn_effort),
  ("test_spawn_base_ref", test_spawn_base_ref),
  ("test_spawn_task_claims_before_launch", test_spawn_task_claims_before_launch),
  ("test_spawn_message_task_body_text_and_ci_flow", test_spawn_message_task_body_text_and_ci_flow),
  ("test_spawned_agent_skips_older_broadcasts", test_spawned_agent_skips_older_broadcasts),
  ("test_spawn_launch_failure_keeps_live_agent", test_spawn_launch_failure_keeps_live_agent),
  ("test_launch_sh_survives_failure_after_hc_run", test_launch_sh_survives_failure_after_hc_run),
  ("test_spawn_task_launch_failure_rolls_back", test_spawn_task_launch_failure_rolls_back),
  ("test_spawn_task_raise_rolls_back", test_spawn_task_raise_rolls_back),
  ("test_agent_without_terminal_reads_as_gone", test_agent_without_terminal_reads_as_gone),
  ("test_spawn_role_set_before_and_shown_in_roster", test_spawn_role_set_before_and_shown_in_roster),
  ("test_rules_appended_to_spawn", test_rules_appended_to_spawn),
  ("test_cold_cache_cheap_cases_and_cold", test_cold_cache_cheap_cases_and_cold),
  ("test_session_turns_keep_cache_warm", test_session_turns_keep_cache_warm),
  ("test_wait_fenced_join_rebinds_dead_hc", test_wait_fenced_join_rebinds_dead_hc),
  ("test_urgent_override", test_urgent_override),
  ("test_wait_wakes_warm_idle", test_wait_wakes_warm_idle),
  ("test_prompt_hook_delivers_and_stops_waiter", test_prompt_hook_delivers_and_stops_waiter),
  ("test_newest_waiter_owns_inbox", test_newest_waiter_owns_inbox),
  ("test_post_to_comms_has_no_sendmessage_nudge", test_post_to_comms_has_no_sendmessage_nudge),
  ("test_sendmessage_ref_and_hookless_waiter", test_sendmessage_ref_and_hookless_waiter),
  ("test_stop_hook_records_ctx", test_stop_hook_records_ctx),
  ("test_board_who", test_board_who),
  ("test_state_json", test_state_json),
  ("test_state_json_round2", test_state_json_round2),
  ("test_state_json_view", test_state_json_view),
  ("test_state_json_running", test_state_json_running),
  ("test_state_json_staffing", test_state_json_staffing),
  ("test_state_json_hc_only_where_shown", test_state_json_hc_only_where_shown),
  ("test_state_json_old_db", test_state_json_old_db)]

end SwarmLean.Tests.Cli.Spawn
