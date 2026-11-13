import Tests.Cli.Fixture
import SwarmLean.Db.Tasks

/-! cli_away_spec.lua: the panel's CLI (board #40): `human` has the communicator's rights; `swarm away` and `--back`;
`state --json --task N`. -/

namespace SwarmLean.Tests.Cli.Away
open SwarmLean.Tests.Cli
open Lean (Json toJson)

def comms (t : T) (name : String := "c") : IO Unit := do
  t.agent name
  t.q_ "insert or replace into meta(k,v) values('comms',?)" [.text name]

def tick (t : T) : IO Unit := t.sw_ "a" ["watchd", "--once", "--comms", "c", "--max-agents", "0"]

def parse (s : String) : IO Json := match Json.parse s with
  | .ok j => pure j
  | .error e => fail s!"not JSON ({e}): {s}"

def state (t : T) (args : List String := []) : IO Json :=
  do parse (← t.sw "human" (["state", "--json"] ++ args)).stdout

def msgsTo (t : T) (who : String) : IO (Array Json) :=
  t.q "select frm, body, urgent from msg where dest=? order by id" [.text who]

/-- Index of the first occurrence of `sub` in `s`. -/
def idx (s sub : String) : Nat := (s.splitOn sub).head!.length

/-- The array's i-th element (null when absent). -/
def nth (j : Json) (i : Nat) : Json := ((j.getArrVal? i).toOption).getD .null

def test_human_ends_agents (t : T) : IO Unit := do
  t.fakes
  t.agent "e" [("status", "idle")]
  has (← t.sw "x" ["end", "e"] { ok := false }).stderr "only the communicator or the user"
  t.sw_ "human" ["end", "e", "--force"]
  eq ((← t.q1 "select status from agent where name='e'").f "status") "ended"
  eq ((← t.q1 "select data from event where kind='end'").f "data") "forced by human"
  eq (← t.q "select 1 x from agent where name='human'").size 0  -- the user is never an agent row

def test_human_is_reserved (t : T) : IO Unit := do
  has (← t.sw "human" ["join"] { ok := false }).stderr "'human' is the user's name"

def test_release_of_anothers_task (t : T) : IO Unit := do
  comms t
  t.agent "e" [("status", "working")]; t.agent "f" [("status", "working")]
  t.sw_ "e" ["task", "add", "x"]; t.sw_ "e" ["task", "claim", "1"]
  has (← t.sw "f" ["task", "release", "1"] { ok := false }).stderr "not claimed by you"  -- a peer can't
  has (← t.sw "human" ["task", "release", "1"]).stdout "released #1 from e"
  eq (← t.q1 "select state, owner from task") (json% {"state": "open"})
  eq (← msgsTo t "e") (json% [{"frm": "human", "body": "the user released #1: stop work on it", "urgent": 1}])
  let ev ← t.q1 "select agent, data from event where kind='release'"
  eq ev (json% {"agent": "human", "data": "#1 from e"})
  -- no one takes it while e is at work and hasn't read the stop (board #53), auto-spawn neither
  has (← t.sw "f" ["task", "claim", "1"] { ok := false }).stderr "released from e, which hasn't read the stop"
  t.q_ "select 1"  -- points SWARM_DB at the test's db
  let c ← connect
  let db ← loadDb c [.task, .agent, .cursor]
  eq (Tasks.pool db).length 0
  t.sw_ "e" ["read"]
  -- the communicator may too, a blocked task as well; its question goes with it
  t.sw_ "f" ["task", "claim", "1"]; t.sw_ "f" ["task", "block", "1", "which db?"]
  t.sw_ "c" ["task", "release", "1"]
  eq (← t.q1 "select state, question from task") (json% {"state": "open"})
  eq (((← msgsTo t "f")[0]!).f "body") "c released #1: stop work on it"
  has (← t.sw "human" ["task", "release", "1"] { ok := false }).stderr "task #1 is not claimed"
  -- an ex-owner that isn't at work holds nothing back: its next turn reads the stop first
  t.q_ "update agent set status='idle' where name='f'"
  t.sw_ "e" ["task", "claim", "1"]

def test_human_drops_and_unblocks (t : T) : IO Unit := do
  t.agent "e"
  t.sw_ "e" ["task", "add", "x"]; t.sw_ "e" ["task", "add", "y"]
  t.sw_ "e" ["task", "claim", "1"]; t.sw_ "e" ["task", "block", "1", "which db?"]
  t.sw_ "human" ["task", "unblock", "1", "--answer", "sqlite"]
  eq (← t.q1 "select state, answer from task where id=1") (json% {"state": "claimed", "answer": "sqlite"})
  eq (((← msgsTo t "e")[0]!).f "frm") "human"
  t.sw_ "e" ["task", "claim", "2"]
  t.sw_ "human" ["task", "drop", "2"]
  eq ((← t.q1 "select state from task where id=2").f "state") "dropped"
  eq ((← t.q1 "select agent from event where kind='drop'").f "agent") "human"

def test_away_queues_questions (t : T) : IO Unit := do
  t.fakes
  comms t
  t.agent "e"
  t.sw_ "e" ["task", "add", "x"]; t.sw_ "e" ["task", "claim", "1"]
  has (← t.sw "human" ["away", "lunch"]).stdout "away: lunch"
  has (← t.sw "human" ["away"]).stdout "already away since"  -- the first since stays
  let told ← msgsTo t "c"
  eq told.size 1  -- told once
  has ((told[0]!).f "body") "the user is away since"; has ((told[0]!).f "body") "(lunch)"; eq ((told[0]!).f "urgent") 0
  let s ← state t
  eq ((s.f "away").f "note") "lunch"
  -- rule 1: task block tells the agent; watchd's notice isn't urgent
  has (← t.sw "e" ["task", "block", "1", "which db?"]).stdout "the user is away: park this"
  tick t
  let n := (← msgsTo t "c")[1]!
  has (n.f "body") "is blocked on #1"; has (n.f "body") "The user is away"; eq (n.f "urgent") 0
  -- rule 2: the communicator's read and board remind it
  has (← t.sw "c" ["read"]).stdout "don't ask them"
  has (← t.sw "c" ["board"]).stdout "the user is away since"
  hasnt (← t.sw "e" ["board"]).stdout "the user is away since"  -- only the communicator

def test_not_away_block_is_urgent (t : T) : IO Unit := do
  t.fakes
  comms t
  t.agent "e"
  t.sw_ "e" ["task", "add", "x"]; t.sw_ "e" ["task", "claim", "1"]
  has (← t.sw "e" ["task", "block", "1", "which db?"]).stdout "watchd tells the communicator"
  tick t
  eq (((← msgsTo t "c")[0]!).f "urgent") 1
  hasnt (← t.sw "c" ["read"]).stdout "the user is away"

def test_away_hc_prompt_not_urgent (t : T) : IO Unit := do
  t.fakes
  t.setHc [json% {"address": "h1", "status": "blocked"}]
  comms t
  t.agent "a" [("hc", "h1"), ("status", "working")]
  t.sw_ "a" ["task", "add", "t1"] { hc := some "h1" }; t.sw_ "a" ["task", "claim", "1"] { hc := some "h1" }
  t.sw_ "human" ["away"]
  tick t
  let m ← t.q "select body, urgent from msg where dest='c' and frm='swarm'"
  eq m.size 1
  has ((m[0]!).f "body") "a prompt or question needs the human"; eq ((m[0]!).f "urgent") 0

def test_back_digest (t : T) : IO Unit := do
  t.fakes
  comms t
  t.agent "e"; t.agent "g"
  for x in ["x", "y", "z"] do t.sw_ "e" ["task", "add", x]
  has (← t.sw "human" ["away", "--back"]).stdout "you were not away"
  t.sw_ "human" ["away"]
  t.sw_ "g" ["task", "claim", "3"]; t.sw_ "g" ["task", "block", "3", "which port?"]  -- #3 asked first
  t.sw_ "e" ["task", "claim", "1"]; t.sw_ "e" ["task", "block", "1", "which db?"]
  t.sw_ "e" ["task", "claim", "2"]; t.sw_ "e" ["task", "done", "2", "--evidence", "abc123"]
  let now := strip (← t.exec ["date", "+%s"]).stdout
  t.q_ s!"update task set pr=12, merged_at={now} where id=2"
  t.q_ "insert into ci(id,sha,status,conclusion,url,created,updated,workflow) values(1,'deadbeef00','completed','success','u','2026-11-11T10:00:00Z','x','ci')"
  t.agent "h"; t.sw_ "h" ["leave"]
  let out := (← t.sw "human" ["away", "--back"]).stdout
  has out "2 questions wait, oldest first:"
  unless subIn out "#3 g" && subIn out "#1 e" && idx out "#3 g" < idx out "#1 e" do fail s!"oldest first: {out}"
  has out "finished: #2 y"; has out "merged: PR #12 (#2)"; has out "main CI: success deadbee"
  has out "ended: h"
  let m ← msgsTo t "c"
  eq m[m.size - 1]! (json% {"frm": "human", "body": "the user is back: 2 questions wait (#3, #1)", "urgent": 1})
  eq (← t.q1 "select v from meta where k='away'") Json.null
  -- state --json keeps the digest for the panel's card until the next away
  let s ← state t
  eq (s.f "away") Json.null
  let b := s.f "back"
  eq (b.f "questions").len 2; eq ((nth (b.f "questions") 0).f "id") 3; eq ((nth (b.f "done") 0).f "id") 2
  eq ((nth (b.f "ended") 0).f "name") "h"; eq ((b.f "ci").f "conclusion") "success"
  t.sw_ "human" ["away"]
  eq ((← state t).f "back") Json.null

-- what happened in away's own second, before it, is not since (board #74): the digest reads event ids
def test_back_digest_exact_since (t : T) : IO Unit := do
  t.fakes
  comms t
  t.agent "e"; t.agent "h"
  t.sw_ "e" ["task", "add", "x"]; t.sw_ "e" ["task", "claim", "1"]; t.sw_ "e" ["task", "done", "1", "--evidence", "abc"]
  t.sw_ "h" ["leave"]
  t.sw_ "human" ["away"]
  t.q_ "update event set ts=(select max(ts) from event)"  -- all in one second
  t.q_ "update task set done_at=(select max(ts) from event)"
  t.q_ "update agent set ended=(select max(ts) from event) where ended is not null"
  t.q_ "update meta set v=(select max(ts) from event)||' ' where k='away'"
  t.sw_ "human" ["away", "--back"]
  let g ← parse (((← t.q1 "select v from meta where k='away_digest'").f "v").s?.getD "")
  eq (g.f "done").len 0; eq (g.f "ended").len 0

def test_state_task (t : T) : IO Unit := do
  t.agent "e"
  t.sw_ "e" ["task", "add", "x", "--body", "do x"]; t.sw_ "e" ["task", "add", "y"]
  t.sw_ "e" ["task", "claim", "1"]
  t.sw_ "e" ["post", "e", "about #1 and #12"]
  t.sw_ "e" ["post", "e", "about #12 only"]
  let s ← state t ["--task", "1"]
  eq ((s.f "task").f "id") 1; eq ((s.f "task").f "body") "do x"
  let kinds := match (s.f "task").f "events" with | .arr a => a.map (fun (x : Json) => x.f "kind") | _ => #[]
  eq kinds (json% ["task-add", "claim"])
  let ms := (s.f "task").f "messages"
  eq ms.len 1; has ((nth ms 0).f "body") "#1 and"
  eq ((← state t ["--task", "9"]).f "task") Json.null

def tests : List Case := [
  ("test_human_ends_agents", test_human_ends_agents),
  ("test_human_is_reserved", test_human_is_reserved),
  ("test_release_of_anothers_task", test_release_of_anothers_task),
  ("test_human_drops_and_unblocks", test_human_drops_and_unblocks),
  ("test_away_queues_questions", test_away_queues_questions),
  ("test_not_away_block_is_urgent", test_not_away_block_is_urgent),
  ("test_away_hc_prompt_not_urgent", test_away_hc_prompt_not_urgent),
  ("test_back_digest", test_back_digest),
  ("test_back_digest_exact_since", test_back_digest_exact_since),
  ("test_state_task", test_state_task)]

end SwarmLean.Tests.Cli.Away
