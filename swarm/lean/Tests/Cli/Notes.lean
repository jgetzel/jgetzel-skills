import Tests.Cli.Spawn

/-! Notes to a task (board #202): `swarm post '#N'` to the live owner, held for the next claim or spawn, or for a done
task to whoever did it, else the communicator; `task show` and `--json` list them. -/

namespace SwarmLean.Tests.Cli.Notes
open SwarmLean.Tests.Cli
open Lean (Json toJson)
open SwarmLean.Sqlite (Val)

/-- The position of `sub` in `s`, or none. -/
def at? (s sub : String) : Option Nat :=
  match s.splitOn sub with
  | a :: _ :: _ => some a.length
  | _ => none

/-- Fails with `msg` unless `b`. -/
def ok (b : Bool) (msg : String) : IO Unit := unless b do fail msg

/-- `task show N --json`. -/
def showJ (t : T) (id : String) : IO Json := do
  match Json.parse (← t.sw "a" ["task", "show", id, "--json"]).stdout with
  | .ok j => return j
  | .error e => fail s!"task show --json: {e}"

def test_note_to_live_owner (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "a" ["task", "add", "t1"]
  t.sw_ "b" ["task", "claim", "1"]
  has (← t.sw "a" ["post", "#1", "job", "j3", "exit 0"]).stdout "posted to #1: to b"
  has (← t.sw "a" ["post", "task:1", "second"]).stdout "posted to #1: to b"
  let r := (← t.sw "b" ["read"]).stdout
  has r "a: [#1] job j3 exit 0"; has r "a: [#1] second"
  eq (← t.q "select agent, path, data from event where kind='task-note' order by id")
    (json% [{"agent": "a", "path": "b", "data": "#1 job j3 exit 0"}, {"agent": "a", "path": "b", "data": "#1 second"}])

-- held on an open task; the next claim prints it after the claim line, once, and not an @all message
def test_note_held_until_claim (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"; t.agent "c"
  t.sw_ "a" ["task", "add", "t1"]
  t.sw_ "a" ["post", "@all", "broadcast"]
  has (← t.sw "a" ["post", "#1", "bench result 4.2s\nfull log in /tmp/x"]).stdout "posted to #1: held for #1's next owner"
  eq (← t.q "select 1 x from msg where dest='b' or dest='c'").size 0
  let out := (← t.sw "b" ["task", "claim", "1"]).stdout
  has out "notes left on #1 for its next owner:"; has out "a: bench result 4.2s\nfull log in /tmp/x"
  hasnt out "broadcast"
  ok (match at? out "claimed #1", at? out "notes left" with | some i, some j => i < j | _, _ => false) "the notes after the claim line"
  hasnt (← t.sw "b" ["read"]).stdout "bench result"  -- given at the claim, not again
  t.sw_ "b" ["task", "release", "1"]
  hasnt (← t.sw "c" ["task", "claim", "1"]).stdout "notes left"  -- delivered once
  let s := (← t.sw "a" ["task", "show", "1"]).stdout
  has s "a (given at claim): bench result 4.2s"; hasnt s "full log"  -- the first line only
  eq (← t.q "select agent, data from event where kind='task-notes-given'") (json% [{"agent": "b", "data": "#1 1"}])

-- the owner gone (its terminal not live, or ended): held, and the next owner's claim prints it
def test_note_owner_gone_held (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"; t.agent "c"
  t.sw_ "a" ["task", "add", "t1"]; t.sw_ "a" ["task", "add", "t2"]
  t.sw_ "b" ["task", "claim", "1"]; t.sw_ "b" ["task", "claim", "2"]
  t.q_ "update agent set hc='h-b' where name='b'"
  t.liveHc ["h-x"]
  has (← t.sw "a" ["post", "#1", "for whoever"]).stdout "posted to #1: held for #1's next owner"
  t.liveHc ["h-b"]
  has (← t.sw "a" ["post", "#2", "to b live"]).stdout "posted to #2: to b"
  t.q_ "update agent set ended=strftime('%s','now') where name='b'"
  has (← t.sw "a" ["post", "#2", "b ended"]).stdout "posted to #2: held for #2's next owner"
  t.q_ "update task set state='open', owner=null"
  has (← t.sw "c" ["task", "claim", "1"]).stdout "a: for whoever"
  let o2 := (← t.sw "c" ["task", "claim", "2"]).stdout
  has o2 "a: b ended"; hasnt o2 "to b live"

-- a done task: whoever did it while live, else the communicator; the poster's own task only recorded
def test_note_done_and_self (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"; t.agent "c"
  t.q_ "insert or replace into meta(k,v) values('comms','c')"
  t.sw_ "a" ["task", "add", "t1"]
  t.sw_ "b" ["task", "claim", "1"]
  has (← t.sw "b" ["post", "#1", "mine"]).stdout "posted to #1: recorded on #1 (you hold it)"
  t.sw_ "b" ["task", "done", "1", "--evidence", "sha"]
  has (← t.sw "a" ["post", "#1", "late result"]).stdout "posted to #1: to b: #1 is done"
  has (← t.sw "b" ["read"]).stdout "a: [#1, done] late result"
  t.q_ "update agent set ended=strftime('%s','now') where name='b'"
  has (← t.sw "a" ["post", "#1", "later"]).stdout "posted to #1: to comms: #1 is done"
  has (← t.sw "c" ["read"]).stdout "a: [#1 is done] later"
  has (← t.sw "c" ["post", "#1", "from comms"]).stdout "recorded on #1 only"
  has (← t.sw "a" ["post", "#9", "x"] { ok := false }).stderr "no task #9"
  eq (← t.q "select coalesce(path, '-') p from event where kind='task-note' order by id")
    (json% [{"p": "-"}, {"p": "b"}, {"p": "c"}, {"p": "-"}])

def test_task_show_lists_notes_json (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "a" ["task", "add", "t1", "--label", "x"]
  t.sw_ "a" ["post", "#1", "one"]
  t.sw_ "b" ["task", "claim", "1"]
  t.sw_ "a" ["post", "#1", "two"]
  t.sw_ "b" ["task", "release", "1"]
  t.sw_ "a" ["post", "#1", "three"]
  let s := (← t.sw "a" ["task", "show", "1"]).stdout
  let i := at? s "a (given at claim): one"; let j := at? s "a (to b): two"; let k := at? s "a (held): three"
  ok (match i, j, k with | some i, some j, some k => i < j && j < k | _, _, _ => false) s!"notes oldest first: {s}"
  let js ← showJ t "1"
  eq (js.f "state") "open"; eq (js.f "labels") (json% ["x"])
  eq ((js.f "notes").getArr?.toOption.getD #[]).size 3
  let ns := ((js.f "notes").getArr?.toOption.getD #[]).map fun n => Json.mkObj [("from", n.f "from"), ("text", n.f "text"),
    ("to", n.f "to"), ("held", n.f "held")]
  eq ns (json% [{"from": "a", "text": "one", "to": "#1", "held": false},
    {"from": "a", "text": "two", "to": "b", "held": false}, {"from": "a", "text": "three", "to": "#1", "held": true}])

-- a spawn with the task: the brief shows the held notes, and they are given once the launch succeeds
def test_spawn_brief_has_held_notes (t : T) : IO Unit := do
  t.fakes
  t.sw_ "a" ["task", "add", "do it"]
  t.sw_ "a" ["post", "#1", "context from the queue"]
  t.sw_ "a" ["spawn", "t-9", "--model", "haiku", "--task", "1"]
  let brief := (Spawn.argvOf (← t.launched)[0]!).getD 2 ""
  has brief "Notes left on #1 for its next owner:"; has brief "a: context from the queue"
  eq (((← showJ t "1").f "notes").getArrVal? 0 |>.toOption.getD .null |>.f "held") false
  eq (← t.q "select agent from event where kind='task-notes-given'") (json% [{"agent": "t-9"}])

-- a launch that fails gives nothing: the note stays held, and the claim after prints it
def test_spawn_failed_launch_keeps_notes_held (t : T) : IO Unit := do
  t.fakes
  Spawn.touch (t.d ++ "/launch.fail")
  t.sw_ "a" ["task", "add", "do it"]
  t.sw_ "a" ["post", "#1", "keep me"]
  discard <| t.sw "a" ["spawn", "t-9", "--model", "haiku", "--task", "1"] { ok := false }
  eq (((← showJ t "1").f "notes").getArrVal? 0 |>.toOption.getD .null |>.f "held") true
  eq (← t.q "select 1 x from event where kind='task-notes-given'").size 0
  has (← t.sw "b" ["task", "claim", "1"]).stdout "a: keep me"

-- a landing task (board #200): to its owner while live, as a claimed one
def test_note_landing_to_owner (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "a" ["task", "add", "t1"]
  t.sw_ "b" ["task", "claim", "1"]
  let sha := strip (← t.git (some t.repo) ["rev-parse", "HEAD"])
  t.sw_ "b" ["task", "land", "1", "--sha", sha]
  has (← t.sw "a" ["post", "#1", "landed?"]).stdout "posted to #1: to b"

def tests : List Case := [
  ("test_note_landing_to_owner", test_note_landing_to_owner),
  ("test_spawn_failed_launch_keeps_notes_held", test_spawn_failed_launch_keeps_notes_held),
  ("test_note_to_live_owner", test_note_to_live_owner),
  ("test_note_held_until_claim", test_note_held_until_claim),
  ("test_note_owner_gone_held", test_note_owner_gone_held),
  ("test_note_done_and_self", test_note_done_and_self),
  ("test_task_show_lists_notes_json", test_task_show_lists_notes_json),
  ("test_spawn_brief_has_held_notes", test_spawn_brief_has_held_notes)]

end SwarmLean.Tests.Cli.Notes
