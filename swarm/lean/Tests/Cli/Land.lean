import Tests.Cli.Fixture

/-! Board #200: `task land` hands a claimed task to a lander (state landing); its lander closes it with `task done`
(evidence on the task's base) or gives it back with `task unland`. -/

namespace SwarmLean.Tests.Cli.Land
open SwarmLean.Tests.Cli
open Lean (Json toJson)

def rev (t : T) (dir : String) : IO String := return strip (← t.git dir ["rev-parse", "HEAD"])

/-- comms is the communicator; a holds task 1, claimed. -/
def setup (t : T) : IO Unit := do
  t.q_ "insert or replace into meta(k,v) values('comms','comms')"
  for n in ["a", "l", "c", "comms"] do t.agent n
  t.sw_ "a" ["task", "add", "fix it"]
  t.sw_ "a" ["task", "claim", "1"]

def state (t : T) (id : Nat) : IO Json := return (← t.q1 "select state from task where id=?" [.int id]).f "state"

def test_land_then_done (t : T) : IO Unit := do
  setup t
  let sha ← rev t t.repo
  let out := (← t.sw "a" ["task", "land", "1", "--sha", sha, "--lander", "l"]).stdout
  has out s!"#1 landing {String.ofList (sha.toList.take 12)} by l since "
  has out "no longer yours"
  eq (← state t 1) "landing"
  let row ← t.q1 "select owner, land_sha, lander, lease_until from task where id=1"
  eq (row.f "owner") "a"; eq (row.f "land_sha") sha; eq (row.f "lander") "l"; eq (row.f "lease_until") Json.null
  eq ((← t.q1 "select count(*) n from event where kind='task-land' and data like '#1 %'").f "n") 1
  has ((← t.q1 "select body from msg where dest='l'").f "body").compress "handed you #1"
  -- the board, task show, state --json and board --json show it
  has (← t.sw "comms" ["board"]).stdout s!"#1 landing {String.ofList (sha.toList.take 12)} by l since "
  has (← t.sw "comms" ["board"]).stdout "(from a)  fix it"
  has (← t.sw "comms" ["task", "show", "1"]).stdout "#1 landing"
  let j := (Json.parse (← t.sw "comms" ["board", "--json"]).stdout).toOption.getD .null
  eq (j.f "view") "board"
  let k := ((j.f "tasks").getArr?.toOption.getD #[]).find? (·.f "id" == toJson 1) |>.getD .null
  eq (k.f "state") "landing"; eq (k.f "land_sha") sha; eq (k.f "lander") "l"
  eq ((j.f "counts").f "landing") 1
  -- not the owner's to hold: it may end, and no claim takes it
  eq (← t.sw "a" ["endable", "--why"] { ok := true }).stdout ""
  has (← t.sw "c" ["task", "claim", "1"] { ok := false }).stderr "task #1 is landing"
  has (← t.sw "a" ["task", "release", "1"] { ok := false }).stderr "not claimed by you"
  -- its lander closes it with a sha on main
  has (← t.sw "l" ["task", "done", "1", "--evidence", sha]).stdout "done #1: landed, handed over by a"
  eq (← state t 1) "done"
  eq ((← t.q1 "select evidence from task where id=1").f "evidence") sha

def test_land_refusals (t : T) : IO Unit := do
  setup t
  let sha ← rev t t.repo
  t.sw_ "a" ["task", "add", "other"]
  has (← t.sw "c" ["task", "land", "1", "--sha", sha] { ok := false }).stderr "task #1 is not yours (a owns it)"
  has (← t.sw "a" ["task", "land", "2", "--sha", sha] { ok := false }).stderr "task #2 is not yours"
  t.q_ "update task set owner='a' where id=2"  -- owned but open: not claimed
  has (← t.sw "a" ["task", "land", "2", "--sha", sha] { ok := false }).stderr "task #2 is open; only a claimed task"
  has (← t.sw "a" ["task", "land", "1", "--sha", "nosuchref"] { ok := false }).stderr "no such commit here"
  has (← t.sw "a" ["task", "land", "1", "--sha", " "] { ok := false }).stderr "--sha is empty"
  eq (← state t 1) "claimed"
  t.sw_ "a" ["task", "land", "1", "--sha", sha]
  has (← t.sw "a" ["task", "land", "1", "--sha", sha] { ok := false }).stderr "task #1 is landing"

def test_wrong_lander (t : T) : IO Unit := do
  setup t
  let sha ← rev t t.repo
  t.sw_ "a" ["task", "land", "1", "--sha", sha, "--lander", "l"]
  for who in ["c", "a"] do  -- an agent without the role, and the former owner
    has (← t.sw who ["task", "done", "1", "--evidence", sha] { ok := false }).stderr "only its lander, an agent with role lander or the communicator"
    has (← t.sw who ["task", "unland", "1", "--why", "x"] { ok := false }).stderr "only its lander"
    has (← t.sw who ["task", "drop", "1"] { ok := false }).stderr "only its lander"
  eq (← state t 1) "landing"
  t.sw_ "c" ["role", "lander for premerge"]  -- any agent with role lander
  t.sw_ "c" ["task", "done", "1", "--evidence", sha]
  eq (← state t 1) "done"
  -- the communicator, with no lander named
  t.sw_ "a" ["task", "add", "two"]; t.sw_ "a" ["task", "claim", "2"]
  t.sw_ "a" ["task", "land", "2", "--sha", sha]
  has (← t.sw "comms" ["board"]).stdout "#2 landing"
  has (← t.sw "comms" ["board"]).stdout "by a lander"
  t.sw_ "comms" ["task", "done", "2", "--evidence", sha]
  eq (← state t 2) "done"

def test_sha_not_on_base (t : T) : IO Unit := do
  setup t
  t.write "b" "new.txt" "work"
  discard <| t.git t.wt ["add", "new.txt"]
  discard <| t.git t.wt ["commit", "-q", "-m", "work"]
  let wsha ← rev t t.wt
  t.sw_ "a" ["task", "land", "1", "--sha", wsha, "--lander", "l"]
  has (← t.sw "l" ["task", "done", "1", "--evidence", wsha] { ok := false }).stderr "not a commit on #1's base"
  has (← t.sw "l" ["task", "done", "1", "--evidence", "lander: queued"] { ok := false }).stderr "not a commit on #1's base"
  eq (← state t 1) "landing"
  discard <| t.git t.repo ["merge", "-q", "--ff-only", wsha]  -- the lander lands it on main
  t.sw_ "l" ["task", "done", "1", "--evidence", wsha]
  eq (← state t 1) "done"

def test_unland (t : T) : IO Unit := do
  setup t
  let sha ← rev t t.repo
  t.sw_ "a" ["task", "land", "1", "--sha", sha, "--lander", "l"]
  has (← t.sw "l" ["task", "unland", "1", "--why", " "] { ok := false }).stderr "--why is empty"
  has (← t.sw "l" ["task", "unland", "1", "--why", "section hpl-x red after rebase"]).stdout "unlanded #1: open again at P1, a and the communicator told"
  let row ← t.q1 "select state, owner, priority, body, land_sha, lander from task where id=1"
  eq (row.f "state") "open"; eq (row.f "owner") Json.null; eq (row.f "priority") 1
  eq (row.f "land_sha") Json.null; eq (row.f "lander") Json.null
  has (row.f "body").compress "by l): section hpl-x red after rebase"
  has ((← t.q1 "select body from msg where dest='a' and frm='l'").f "body").compress "could not land #1"
  has ((← t.q1 "select body from msg where dest='comms' and frm='l'").f "body").compress "(a handed it over.)"
  eq ((← t.q1 "select count(*) n from event where kind='task-unland'").f "n") 1
  has (← t.sw "l" ["task", "unland", "1", "--why", "x"] { ok := false }).stderr "task #1 is open; only a landing task"
  -- claimable again; a P0 task stays P0
  t.sw_ "c" ["task", "claim", "1"]
  t.sw_ "c" ["task", "priority", "1", "0"]
  t.sw_ "c" ["task", "land", "1", "--sha", sha]
  t.sw_ "comms" ["task", "unland", "1", "--why", "again"]
  eq ((← t.q1 "select priority from task where id=1").f "priority") 0

def test_dependants_wait_until_done (t : T) : IO Unit := do
  setup t
  let sha ← rev t t.repo
  t.sw_ "a" ["task", "add", "next", "--after", "1"]
  t.sw_ "a" ["task", "land", "1", "--sha", sha, "--lander", "l"]
  has (← t.sw "c" ["task", "claim", "2"] { ok := false }).stderr "#2 waits on #1 (landing"
  t.sw_ "l" ["task", "done", "1", "--evidence", sha]
  t.sw_ "c" ["task", "claim", "2"]

def test_land_frees_the_owner_but_not_a_dirty_worktree (t : T) : IO Unit := do
  t.q_ "insert or replace into meta(k,v) values('comms','comms')"
  t.agent "e" [("wt", t.wt)]
  t.setCwd "e" t.wt
  t.sw_ "e" ["task", "add", "x"]; t.sw_ "e" ["task", "claim", "1"]
  t.write "e" "new.txt" "work"
  discard <| t.git t.wt ["add", "new.txt"]
  discard <| t.git t.wt ["commit", "-q", "-m", "work"]
  let r ← t.sw "e" ["endable", "--why"] { ok := false }
  has r.stdout "claim held (#1)"
  t.sw_ "e" ["task", "land", "1", "--sha", ← rev t t.wt]
  eq (← t.sw "e" ["endable", "--why"] { ok := true }).stdout ""  -- its commits are the lander's to land
  t.write "e" "more.txt" "wip"
  has (← t.sw "e" ["endable", "--why"] { ok := false }).stdout "dirty worktree"

def test_landing_late_told_once (t : T) : IO Unit := do
  setup t
  let sha ← rev t t.repo
  t.sw_ "a" ["task", "land", "1", "--sha", sha, "--lander", "l"]
  let late := "select count(*) n from msg where dest='comms' and body like '%has waited%'"
  t.sw_ "a" ["watchd", "--once", "--comms", "comms", "--max-agents", "0"]
  eq ((← t.q1 late).f "n") 0  -- not yet 2 h
  t.q_ "update task set landing_at=landing_at-7300 where id=1"
  t.sw_ "a" ["watchd", "--once", "--comms", "comms", "--max-agents", "0"]
  t.sw_ "a" ["watchd", "--once", "--comms", "comms", "--max-agents", "0"]
  eq ((← t.q1 late).f "n") 1
  has ((← t.q1 "select body from msg where dest='comms' and body like '%has waited%'").f "body").compress "#1 landing"

def tests : List Case := [
  ("test_land_then_done", test_land_then_done),
  ("test_land_refusals", test_land_refusals),
  ("test_wrong_lander", test_wrong_lander),
  ("test_sha_not_on_base", test_sha_not_on_base),
  ("test_unland", test_unland),
  ("test_dependants_wait_until_done", test_dependants_wait_until_done),
  ("test_land_frees_the_owner_but_not_a_dirty_worktree", test_land_frees_the_owner_but_not_a_dirty_worktree),
  ("test_landing_late_told_once", test_landing_late_told_once)]

end SwarmLean.Tests.Cli.Land
