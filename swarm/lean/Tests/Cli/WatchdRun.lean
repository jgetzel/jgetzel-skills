import Tests.Cli.Fixture
import SwarmLean.Lib.Cost

/-! cli_watchd_run_spec.lua: CLI tests ported from test_swarm.py (fake_proc .. test_run_remote_job_telemetry): one
watchd, machine note, memory pressure, CI red tasks, swarm run. -/

namespace SwarmLean.Tests.Cli.WatchdRun
open SwarmLean.Tests.Cli
open Lean (Json toJson)
open SwarmLean.Sqlite (Val)

/-- Epoch seconds. -/
def now (t : T) : IO Int := return (strip (← t.exec ["date", "+%s"]).stdout).toInt!

def myPid : IO Int := return Int.ofNat (← IO.Process.getPID).toNat

def parse (s : String) : IO Json := match Json.parse s with
  | .ok j => pure j
  | .error e => fail s!"not JSON ({e}): {s}"

def nth (j : Json) (i : Nat) : Json := ((j.getArrVal? i).toOption).getD .null

def arr (j : Json) : Array Json := match j with | .arr a => a | _ => #[]

/-- util.slurp of the joined path, asserted. -/
def readF (parts : List String) : IO String := do
  match ← slurp ("/".intercalate parts) with
  | some s => pure s
  | none => fail s!"cannot read {"/".intercalate parts}"

def mkdir (p : String) : IO Unit := IO.FS.createDirAll p

def exists_ (p : String) : IO Bool := (p : System.FilePath).pathExists

def lines (s : String) : Nat := (splitlines s).length

/-- Lua pattern pieces, enough for these tests. -/
inductive Tok
  | lit (s : String)
  | one (p : Char → Bool)
  | many (p : Char → Bool)
  | star

partial def mt : List Tok → List Char → Bool
  | [], _ => true
  | .lit s :: ts, cs => let l := s.toList; cs.take l.length == l && mt ts (cs.drop l.length)
  | .one p :: ts, c :: cs => p c && mt ts cs
  | .one _ :: _, [] => false
  | .many p :: ts, cs =>
    let n := (cs.takeWhile p).length
    (List.range n).any fun k => mt ts (cs.drop (n - k))
  | .star :: ts, cs => (List.range (cs.length + 1)).any fun k => mt ts (cs.drop k)

/-- Lua's s:find(pattern) (anchored: a leading ^). -/
def finds (anch : Bool) (toks : List Tok) (s : String) : Bool :=
  if anch then mt toks s.toList else (List.range (s.length + 1)).any fun i => mt toks (s.toList.drop i)

def digit (c : Char) : Bool := c.isDigit
def hex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def pad2 (n : Nat) : String := if n < 10 then s!"0{n}" else s!"{n}"

def fakeProc (t : T) (availKb : Nat := 20000000) (psi : String := "1.0") : IO String := do
  let r := t.d ++ "/proc"
  mkdir (r ++ "/pressure")
  put (r ++ "/uptime") "10000.0 0\n"
  put (r ++ "/meminfo") s!"MemTotal: 32000000 kB\nMemAvailable: {availKb} kB\n"
  for k in ["memory", "cpu"] do
    put (r ++ "/pressure/" ++ k) s!"some avg10={psi} avg60=0 avg300=0 total=0\n"
  discard <| t.fake "ps" "#!/bin/sh\ncat \"$SWARM_PROC\"/[0-9]*/ps 2>/dev/null; exit 0\n"  -- machine.procs() reads the fixture
  return r

structure PO where
  ageS : Nat := 240
  rssPages : Nat := 0
  cwd : Option String := none

def addProc (t : T) (r : String) (pid ppid : Nat) (comm : String) (argv : List String) (o : PO := {}) : IO Unit := do
  let tck := (strip (← t.exec ["getconf", "CLK_TCK"]).stdout).toNat!
  let d := s!"{r}/{pid}"
  mkdir d
  let f := ["S", toString ppid] ++ List.replicate 17 "0" ++ [toString ((10000 - o.ageS) * tck), "0", toString o.rssPages]
  put (d ++ "/stat") s!"{pid} ({comm}) {" ".intercalate f}"
  put (d ++ "/cmdline") ("\x00".intercalate argv ++ "\x00")
  put (d ++ "/oom_score_adj") "0"
  put (d ++ "/ps") s!"{pid} {ppid} {o.rssPages * 4} {o.ageS / 60}:{pad2 (o.ageS % 60)} 0:00 {" ".intercalate argv}\n"
  if let some c := o.cwd then discard <| t.exec ["ln", "-s", c, d ++ "/cwd"]

def swp (t : T) (who proc : String) (args : List String) (o : Opts := {}) : IO R :=
  t.sw who args { o with env := o.env ++ [("SWARM_PROC", some proc)] }

def hookp (t : T) (who proc cmd : String) : IO Json := do
  let base := json% {"tool_name": "Bash", "tool_input": {"command": $cmd}}
  let payload := match ← t.cwdOf? who with | some c => base.setObjVal! "cwd" (Json.str c) | none => base
  let r ← swp t who proc ["hook", "pre-tool"] { stdin := some payload.compress }
  if strip r.stdout == "" then return Json.mkObj []
  return (← parse r.stdout).f "hookSpecificOutput"

def commsTick (t : T) : IO Unit := t.sw_ "a" ["watchd", "--once", "--comms", "comms", "--max-agents", "0"]

def idle (t : T) (name : String) (kw : List (String × Val) := []) : IO Unit := do
  let old := (← now t) - 3600
  let extra : List (String × Val) := [("status", "idle"), ("last_active", .int old)]
  t.agent name (kw.filter (fun (k, _) => k != "status" && k != "last_active") ++ extra)

def ended (t : T) (name : String) : IO Bool := do
  return (← t.q1 "select ended e from agent where name=?" [.text name]).f "e" != .null

def rev (t : T) : IO String := return strip (← t.git t.repo ["rev-parse", "HEAD"])

def test_one_watchd (t : T) : IO Unit := do
  t.sw_ "a" ["join"]
  t.q_ "insert or replace into meta(k,v) values('watchd',?)" [.text s!"{← myPid} T1"]  -- a live pid
  let r ← t.sw "a" ["watchd", "--once"] { ok := false }
  has r.stderr "already runs"; has r.stderr "T1"
  t.sw_ "a" ["watchd", "--once", "--takeover"]
  hasnt ((← t.q1 "select v from meta where k='watchd'").f "v") "T1"

-- sw-global §4: the machine's one watchd runs every live swarm's passes in one tick (a gone agent of each reaped); a
-- swarm's --ci and --model are its own meta; each hour it copies the db to swarm.db.bak beside it
def test_one_watchd_serves_every_swarm (t : T) : IO Unit := do
  t.fakes
  t.setHc [json% {"address": "t5"}]
  t.sw_ "zz" ["new", "u"]
  t.sw_ "a" ["join"] { env := [("SWARM", some "t")] }
  t.sw_ "x" ["join"] { env := [("SWARM", some "u")] }
  t.q_ "update agent set hc='t1' where name='a'"
  t.q_ "update agent set hc='t2' where name='x'"
  t.sw_ "a" ["watchd", "--once"]
  eq ((← t.q1 "select count(*) n from agent where ended is not null").f "n") 2
  eq ((← t.q1 "select swarm from agent where name='x'").f "swarm") "u"
  t.sw_ "a" ["watchd", "--once", "--ci", "--model", "haiku"] { env := [("SWARM", some "u")] }
  eq ((← t.q1 "select v from meta where scope='u' and k='ci'").f "v") "on"
  eq ((← t.q1 "select v from meta where scope='u' and k='spawn_model'").f "v") "haiku"
  eq (← t.q "select 1 from meta where scope='t' and k in ('ci', 'spawn_model')").size 0
  let bak := t.db ++ ".bak"
  eq (← exists_ bak) true
  eq (← exists_ (t.db ++ ".tmp")) false
  let c ← SwarmLean.Sqlite.Conn.open bak true
  let rows ← c.query "select count(*) from swarm"
  eq (match rows[0]?.bind (·[0]?) with | some (.int n) => n | _ => -1) 2

-- review of #75: swarm t's reap read only t's agents and reopened a lapsed claim of u's live agent x
def test_watchd_leaves_another_swarms_claim (t : T) : IO Unit := do
  t.fakes
  t.setHc [json% {"address": "t5"}]
  t.sw_ "zz" ["new", "u"]
  t.sw_ "a" ["join"] { env := [("SWARM", some "t")] }
  t.sw_ "x" ["join"] { env := [("SWARM", some "u")] }
  t.q_ "update agent set hc='t5', status='working' where name='x'"
  t.q_ "insert into task(title, state, owner, lease_until, created_by) values('w', 'in_progress', 'x', 1, 'x')"
  t.sw_ "a" ["watchd", "--once"]
  let r ← t.q1 "select state, owner from task where title='w'"
  eq (r.f "state") "in_progress"
  eq (r.f "owner") "x"

def test_machine_note_and_patterns (t : T) : IO Unit := do
  let pr ← fakeProc t
  discard <| t.hook "a" "session"; discard <| t.hook "b" "session"
  t.q_ "update agent set claude_pid=100 where name='a'"
  addProc t pr 100 1 "claude" ["claude"]
  addProc t pr 101 100 "bash" ["bash", "-c", "x"]
  addProc t pr 102 101 "cabal" ["/nix/store/x/bin/cabal", "build"] { rssPages := 1000000 / 4 }
  addProc t pr 103 101 "my-build-script" ["./my-build-script", "all"] { rssPages := 2000000 / 4 }  -- no word names it
  addProc t pr 150 1 "claude" ["claude"]  -- someone's own session
  addProc t pr 200 150 "node" ["node", "/x/bin/tsc", "-b"] { rssPages := 500000 / 4 }
  -- no history: nothing is printed, whatever the command
  eq (← hookp t "a" pr "nix develop -c env X=1 cabal build") (Json.mkObj [])
  eq (← hookp t "a" pr "./my-build-script all") (Json.mkObj [])
  -- history here: a small command is silent, one predicted above half of the 19.1G available speaks
  let host ← SwarmLean.Shim.hostname
  let repo := ((← (SwarmLean.Cost.repoName (some (← t.cwdOf "a")) : App _).run.run (← Ctx.new))
    |> fun r => match r with | .ok (some n) => n | _ => "")
  for (cmd, gb) in [("cabal build", 1), ("./my-build-script all", 12)] do
    let ts ← now t
    let rec_ : SwarmLean.Cost.Rec := { ts, machine := host, repo, agent := "b", cmd, wall_s := 360, peak_kb := gb * 1048576 }
    match ← ((SwarmLean.Cost.record rec_ : App Bool).run.run (← Ctx.new)) with
    | .ok _ => pure ()
    | .error _ => fail "cost.record exited"
  let hk (cmd : String) := hookp t "a" pr cmd
  eq (← hk "cabal build") (Json.mkObj [])
  eq (← hk "git commit -m 'make it'") (Json.mkObj [])
  let o ← hk "cd /x && ./my-build-script all 2>&1 | tail"
  eq (o.f "permissionDecision") Json.null
  let n := (o.f "additionalContext").s?.getD ""
  has n "`./my-build-script all` took ~12.0G and 6 min the last 1 time here; 19.1G is available now."
  has n "machine: 19.1/30.5G"
  has n "a 2.9G (my-build-script all 1.9G)"  -- the claude process counts; the largest process is named by size
  has n "other session 0.5G (tsc -b 0.5G)"
  unless lines n ≤ 7 do fail n

def test_pressure_edge_oom_and_orphans (t : T) : IO Unit := do
  let pr ← fakeProc t 2000000  -- 6% available: high
  discard <| t.hook "a" "session"; discard <| t.hook "b" "session"
  t.q_ "update agent set claude_pid=100 where name='a'"
  addProc t pr 100 1 "claude" ["claude"]
  addProc t pr 102 100 "cabal" ["cabal", "build"] { rssPages := 1000000 / 4 }
  -- b is ended; its worktree holds a build reparented to init
  t.q_ "update agent set ended=1 where name='b'"
  addProc t pr 300 1 "ghc-9.10.3" ["ghc-9.10.3", "--make"] { rssPages := 3000000 / 4, cwd := some t.wt }  -- in no agent's scope
  addProc t pr 301 1 "ghc-9.10.3" ["ghc-9.10.3", "--make"] { rssPages := 3000000 / 4, cwd := some t.wt }  -- in b's scope
  addProc t pr 302 1 "ghc-9.10.3" ["ghc-9.10.3", "--make"] { rssPages := 3000000 / 4, cwd := some t.wt }  -- in b's job scope
  addProc t pr 303 4000 "make" ["make"] { cwd := some t.wt }  -- in b's scope, adopted by a subreaper (systemd --user), not init
  addProc t pr 304 1 "sleep" ["sleep", "600"] { cwd := some t.wt }  -- reparented to init, but in live a's scope
  discard <| t.fake "kill" ("#!/bin/sh\necho \"$*\" >>" ++ t.d ++ "/kills\n")  -- no signal reaches the machine
  put (pr ++ "/300/cgroup") "0::/user.slice/user-1000.slice/session-1.scope\n"
  put (pr ++ "/301/cgroup") "0::/user.slice/app.slice/swarm-agent-b-4242.scope\n"
  put (pr ++ "/302/cgroup") "0::/user.slice/app.slice/swarm-job-b-j3.scope\n"
  put (pr ++ "/303/cgroup") "0::/user.slice/app.slice/swarm-agent-b-4242.scope\n"
  put (pr ++ "/304/cgroup") "0::/user.slice/app.slice/swarm-agent-a-5151.scope\n"
  discard <| swp t "a" pr ["watchd", "--once"]
  let ev := (← t.q "select kind from event where kind in ('pressure','pressure-end','orphan-kill') order by id").map (·.f "kind")
  eq ev (json% ["pressure", "orphan-kill", "orphan-kill", "orphan-kill"])
  has ((← t.q1 "select data from event where kind='orphan-kill'").f "data") "301 "
  eq (← readF [t.d, "kills"]) "-TERM 301\n-TERM 302\n-TERM 303\n"  -- only those in b's agent and job scopes, whatever their parent
  let notes ← t.q "select dest,body from msg where kind='notice'"
  eq notes.size 1; eq ((notes[0]!).f "dest") "a"; has ((notes[0]!).f "body") "ghc-9.10.3"
  eq (← readF [pr, "102", "oom_score_adj"]) "500"
  eq (← readF [pr, "300", "oom_score_adj"]) "0"  -- not an agent's: left alone
  -- still high: no second notice (edge-triggered); leaves high: pressure-end
  discard <| swp t "a" pr ["watchd", "--once"]
  eq ((← t.q1 "select count(*) n from event where kind='pressure'").f "n") 1
  discard <| fakeProc t 20000000
  discard <| swp t "a" pr ["watchd", "--once"]
  eq ((← t.q1 "select count(*) n from event where kind='pressure-end'").f "n") 1

def test_machine_line_at_decisions (t : T) : IO Unit := do
  let pr ← fakeProc t
  discard <| t.hook "a" "session"
  t.sw_ "a" ["task", "add", "x"]; t.sw_ "a" ["task", "add", "y"]
  has (← swp t "a" pr ["board"]).stdout "machine: 19.1/30.5G"
  let c := (← swp t "a" pr ["task", "claim", "1"]).stdout
  has c "machine: 19.1/30.5G"; hasnt c "started in the last"
  discard <| fakeProc t 2000000  -- high pressure: the full note
  addProc t pr 100 1 "claude" ["claude"]
  has (← swp t "a" pr ["task", "claim", "2"]).stdout "machine: 1.9/30.5G"

def test_pressure_notice_reaches_stayers (t : T) : IO Unit := do
  let pr ← fakeProc t 2000000
  discard <| t.hook "a" "session"; discard <| t.hook "s" "session"
  t.q_ "update agent set stay='review' where name='s'"
  discard <| swp t "a" pr ["watchd", "--once"]
  eq ((← t.q1 "select count(*) n from msg where kind='notice' and dest='s'").f "n") 1

def test_ci_red_is_one_task_closed_on_green (t : T) : IO Unit := do
  let commit (who : String) : IO Unit :=
    discard <| t.git t.repo ["commit", "-q", "--allow-empty", "-m", s!"x\n\nSwarm-Agent: {who}"]
  let green ← rev t
  commit "a"; commit "gone"
  let red ← rev t
  let mut runs : Array Json := #[
    json% {"databaseId": 9, "headSha": $red, "conclusion": "failure", "status": "completed", "url": "http://ci/9",
      "createdAt": "2026-11-08T10:05:00Z", "updatedAt": "2026-11-08T10:08:00Z", "event": "push"},
    json% {"databaseId": 8, "headSha": $green, "conclusion": "success", "status": "completed", "url": "http://ci/8",
      "createdAt": "2026-11-08T10:00:00Z", "updatedAt": "2026-11-08T10:03:00Z", "event": "push"}]
  let gh (rs : Array Json) : IO Unit := discard <| t.fake "gh"
    s!"#!/bin/sh\n[ \"$1\" = api ] && echo '{(Json.arr rs).compress}' || echo 'step Build failed'\n"
  gh runs
  t.agent "a"; t.agent "gone" [("ended", .int 1)]; t.agent "comms"
  let go : IO Unit := t.sw_ "a" ["watchd", "--once", "--ci", "--comms", "comms"] { cwd := some t.repo }
  let reset : IO Unit := t.q_ "delete from meta where k like 'ci%'"
  t.sw_ "a" ["task", "add", "earlier work"]
  go; go  -- second tick: edge-triggered
  let m ← t.q "select dest,body from msg where kind='system' order by id"
  eq m.size 1; eq ((m[0]!).f "dest") "a"
  has ((m[0]!).f "body") "http://ci/9"; has ((m[0]!).f "body") "swarm task claim 2"
  let redTasks ← t.q "select id,body,state from task where title like 'main red:%'"
  eq redTasks.size 1; has ((redTasks[0]!).f "body") "Build failed"
  eq (← t.q "select repo from task_repo where task=2") (json% [{"repo": $(t.repo)}]) "the red task is the repo's"
  let board := (← t.sw "a" ["board"]).stdout
  unless subIn board "main red" && subIn board "earlier work" && (board.splitOn "main red").head!.length <
      (board.splitOn "earlier work").head!.length do fail "the red task starts first"
  -- a later red in the same stretch is the same task
  let later := ((runs[0]!.setObjVal! "databaseId" (10 : Int)).setObjVal! "createdAt" "2026-11-08T10:10:00Z")
  runs := #[later] ++ runs
  gh runs; reset; go
  eq (← t.q "select 1 x from task where title like 'main red:%'").size 1
  eq (← t.q "select 1 x from msg where kind='system'").size 1
  has ((← t.q1 "select body from task where id=2").f "body") "Later red: run 10"
  -- the fixer's done releases the task to Backlog, and the agent can stop; a re-run of the reds leaves an older green
  -- on top: still in Backlog
  t.sw_ "a" ["task", "claim", "2"]
  has (← t.sw "a" ["task", "done", "2", "--evidence", "abc"]).stdout "released"
  let row ← t.q1 "select state,owner,hold from task where id=2"
  eq (toJson [row.f "state", row.f "owner", row.f "hold"]) (json% ["backlog", null, "abc awaiting a green run"])
  eq (← t.q "select 1 x from event where kind='red-fixed' and data='#2 abc'").size 1
  eq (← t.sw "a" ["endable", "--why"] { ok := true }).stdout ""
  let rerun := runs.map fun r =>
    if r.f "conclusion" == Json.str "failure" then (r.setObjVal! "status" "in_progress").setObjVal! "conclusion" Json.null else r
  gh rerun; reset; go
  eq ((← t.q1 "select state from task where id=2").f "state") "backlog"
  eq ((← t.q1 "select hold from task where id=2").f "hold") "abc awaiting a green run"
  -- a red run from before the fix leaves the hold; one after it clears it
  let old := (runs[0]!.setObjVal! "databaseId" (12 : Int)).setObjVal! "createdAt" "2026-11-08T10:12:00Z"
  runs := #[old] ++ runs
  gh runs; reset; go
  has ((← t.q1 "select body from task where id=2").f "body") "Later red: run 12"
  eq ((← t.q1 "select hold from task where id=2").f "hold") "abc awaiting a green run"
  let newer := (runs[0]!.setObjVal! "databaseId" (13 : Int)).setObjVal! "createdAt" "2099-01-01T00:00:00Z"
  runs := #[newer] ++ runs
  gh runs; reset; go
  has ((← t.q1 "select body from task where id=2").f "body") "Later red: run 13"
  eq ((← t.q1 "select state, hold from task where id=2")) (json% {"state": "ready"})  -- back in Ready, its note gone
  -- fixed again: a green run closes the held, unowned task and clears its hold
  t.sw_ "a" ["task", "claim", "2"]
  t.sw_ "a" ["task", "done", "2", "--evidence", "def"]
  eq ((← t.q1 "select hold from task where id=2").f "hold") "def awaiting a green run"
  let g := ((runs[0]!.setObjVal! "databaseId" (14 : Int)).setObjVal! "conclusion" "success").setObjVal! "createdAt"
    "2099-06-01T00:00:00Z"
  runs := #[g] ++ runs
  gh runs; reset; go
  let d ← t.q1 "select state,evidence,hold from task where id=2"
  let want := s!"green run 14 at {red.take 7}"
  eq (toJson [d.f "state", d.f "evidence", d.f "hold"]) (json% ["completed", $want, null])
  -- no live suspect: a new task, and comms hears of it
  t.q_ "update agent set ended=1 where name='a'"; t.q_ "delete from event where kind='ci-red'"
  runs := runs.extract 1 runs.size
  gh runs; reset; t.q_ "delete from ci"
  go
  let dests := (← t.q "select dest from msg where kind='system' order by id").map (·.f "dest")
  eq dests (json% ["a", "comms"])
  eq (← t.q "select 1 x from task where title like 'main red:%' and state='ready'").size 1

-- board #136: tasks are the machine's, but each repo's CI passes act only on its own (task_repo): repo B's open red
-- task neither takes A's red run nor closes on A's green one, A's red gets its own task, and A's merged PR from a/2
-- leaves B's claim #2 alone
def test_ci_acts_only_on_the_repos_tasks (t : T) : IO Unit := do
  let sha ← rev t
  let run (id : Nat) (concl at_ : String) : Json :=
    json% {"databaseId": $id, "headSha": $sha, "conclusion": $concl, "status": "completed", "url": "http://ci/a",
      "createdAt": $at_, "updatedAt": $at_, "event": "push"}
  let pr := (json% [{"number": 4, "headRefName": "a/2", "headRefOid": $sha, "baseRefName": "main", "state": "MERGED",
    "mergedAt": "2026-11-08T10:00:00Z", "mergeCommit": {"oid": $sha}, "statusCheckRollup": []}]).compress
  let gh (rs : Array Json) : IO Unit := discard <| t.fake "gh"
    s!"#!/bin/sh\ncase \"$1\" in api) echo '{(Json.arr rs).compress}';; pr) echo '{pr}';; *) echo 'step Build failed';; esac\n"
  t.agent "a"; t.agent "comms"
  t.q_ "insert into task(title, body, state, created_by) values('main red: run 5', 'b', 'ready', 'swarm')"
  t.q_ "insert into task(title, state, owner, first_claimed_at) values('b work', 'in_progress', 'a', 1)"
  -- B's alone: the fixture's task_of_repo trigger put both in this repo too
  t.q_ "delete from task_repo where task in (1, 2)"
  t.q_ "insert into task_repo(task, repo) values(1, '/elsewhere/b'), (2, '/elsewhere/b')"
  let go : IO Unit := t.sw_ "a" ["watchd", "--once", "--ci", "--comms", "comms"] { cwd := some t.repo }
  gh #[run 9 "failure" "2026-11-08T10:05:00Z"]
  go
  eq ((← t.q1 "select body from task where id=1").f "body") "b"
  eq ((← t.q1 "select state from task where id=2").f "state") "in_progress"
  eq (← t.q "select id from task where title like 'main red: run 9%'") (json% [{"id": 3}])
  eq (← t.q "select repo from task_repo where task=3") (json% [{"repo": $(t.repo)}])
  gh #[run 10 "success" "2026-11-08T10:10:00Z", run 9 "failure" "2026-11-08T10:05:00Z"]
  t.q_ "delete from meta where k like 'ci%'"
  go
  eq ((← t.q1 "select state from task where id=1").f "state") "ready"
  eq ((← t.q1 "select state from task where id=3").f "state") "completed"

-- ---- swarm run ----
-- Fake hc and ssh: the 'laptop' is a home dir here; rsync is real. Per-terminal `hc get` answers come from <d>/get.<terminal>.
def fakeRemote (t : T) (state : String := "connected") : IO String := do
  let home := t.d ++ "/laptop-home"
  mkdir home
  let H := shquote home; let D := shquote t.d
  let m := (json% {"machines": [{"name": "laptop", "state": $state, "target": "u@laptop"}]}).compress
  let sub (s : String) := ((s.replace "@D" D).replace "@H" H).replace "@M" m
  discard <| t.fake "hc" (sub r#"#!/bin/sh
echo "$*" >> @D/hc.log
case "$1 $2" in "machine ls") echo '@M'; exit 0;; esac
case "$1" in
  ls) echo '{"terminals": []}';;
  run) while [ "$1" != sh ]; do shift; done
    (cd @H && env -u XDG_STATE_HOME HOME=@H "$@" >/dev/null); echo $? > @D/rc; echo '{"address": "laptop/t1"}';;
  wait) [ -e @D/lost ] && exit 3
    echo "{\"ended\": true, \"exit_code\": $(cat @D/rc)}";;
  get) if [ -f @D/get.$2 ]; then cat @D/get.$2; else echo '{"error": {"kind": "not_found", "message": "no terminal"}}'; exit 3; fi;;
  exec) [ -e @D/exec.fail ] && exit 1; while [ "$1" != --timeout ]; do shift; done; shift 2; cd @H && env -u XDG_STATE_HOME HOME=@H "$@" 2>/dev/null;;
esac
"#)
  discard <| t.fake "ssh" (sub r#"#!/bin/sh
while [ "$1" = -o ] || [ "$1" = -l ]; do shift 2; done
shift; cd @H && HOME=@H exec sh -c "$*"
"#)
  return home

def test_run_remote_syncs_runs_and_brings_back (t : T) : IO Unit := do
  let home ← fakeRemote t
  let hclog := t.d ++ "/hc.log"
  mkdir (t.wt ++ "/.claude")
  put (t.wt ++ "/.claude/swarm.json") (json% {"run": {"prefix": "env", "env": ["^APP_"], "set": {"T": "{dir}/target"},
    "bring_back": ["out/"]}}).compress
  t.write "b" ".gitignore" "out/\nsecret.txt\n"; t.write "b" "secret.txt" "s"
  t.sw_ "b" ["task", "add", "t"]; t.sw_ "b" ["task", "claim", "1"]
  let cmd := "echo \"app=$APP_Y k=$K t=$T\"; echo new > new.txt; echo job > a.txt; mkdir -p out; echo r > out/r.txt; " ++
    s!"echo mine > {t.wt}/b.txt; echo theirs > b.txt; exit 3"
  let r ← t.sw "b" ["run", "--on", "laptop", "--env", "K=1", "--", cmd] { ok := false, env := [("APP_Y", some "2")] }
  eq r.code 3 r.stderr
  let src := home ++ "/.cache/swarm-run/repo/wt/src"
  has r.stdout s!"app=2 k=1 t={home}/.cache/swarm-run/repo/wt/target"
  unless finds false ([Tok.lit "job j1 exit 3 on laptop, 0m", .one digit, .one digit, .lit "s (sync "] ++ [Tok.many fun c => c.isDigit || c == '.']
      ++ [.lit "s, back ", .many fun c => c.isDigit || c == '.', .lit "s), tree "] ++ List.replicate 7 (Tok.one hex) ++ [.lit "; log: "]) r.stdout do
    fail r.stdout
  if ← exists_ (src ++ "/secret.txt") then fail "ignored files stay here"
  eq (toJson [← readF [t.wt, "new.txt"], ← readF [t.wt, "a.txt"], ← readF [t.wt, "out/r.txt"]]) (json% ["new\n", "job\n", "r\n"])
  eq (← readF [t.wt, "b.txt"]) "mine\n"  -- edited here during the job: kept, theirs beside the log
  eq (← readF [t.d, "jobs", "1", "kept", "b.txt"]) "theirs\n"
  has r.stdout "b.txt are in"
  let rows ← t.q "select kind,data from event where kind like 'job-%'"
  let evOf (k : String) : IO Json := do
    match rows.find? (fun x => x.f "kind" == Json.str k) with
    | some row => parse ((row.f "data").s?.getD "")
    | none => fail s!"no {k} event"
  let st ← evOf "job-start"; let en ← evOf "job-end"
  eq (toJson [st.f "machine", st.f "task", st.f "hc"]) (json% ["laptop", 1, "laptop/t1"])
  eq (toJson [en.f "exit", Json.num (((en.f "tree").s?.getD "").length : Nat)]) (json% [3, 40])
  let hc ← readF [hclog]
  has hc "--label swarm-agent=b --label swarm-job=1 --label swarm-wt=repo/wt --label swarm-task=1"
  has hc "rm laptop/t1"
  has hc "< /dev/null"  -- the job reads EOF, not the hc terminal (board #212)
  for j in arr ((← parse (← t.sw "b" ["state", "--json"]).stdout).f "running") do
    eq (j.f "machine") Json.null

def test_run_never_ran_or_lost_is_255 (t : T) : IO Unit := do
  discard <| fakeRemote t "disconnected"
  let r ← t.sw "b" ["run", "--on", "laptop", "--", "true"] { ok := false }
  eq r.code 255
  has r.stderr "laptop is disconnected; the job never ran"
  eq ((← t.q1 "select count(*) n from event where kind like 'job-%'").f "n") 0
  discard <| fakeRemote t
  put (t.d ++ "/lost") ""
  let r ← t.sw "b" ["run", "--on", "laptop", "--", "true"] { ok := false }
  eq r.code 255
  has r.stdout "lost on laptop"; has r.stdout "hc wait laptop/t1"
  eq ((← parse (((← t.q1 "select data from event where kind='job-end'").f "data").s?.getD "")).f "exit") "lost"

def test_run_local_records_job (t : T) : IO Unit := do
  let r ← t.sw "b" ["run", "--", "echo hi; exit 2"] { ok := false }
  eq r.code 2
  unless finds true ([Tok.lit "hi\njob j1 exit 2 on this machine, ", .star, .lit "tree "] ++ List.replicate 7 (Tok.one hex)) r.stdout do
    fail r.stdout
  let ks := (← t.q "select kind from event where kind like 'job-%' order by id").map (·.f "kind")
  eq ks (json% ["job-start", "job-end"])

/-- A tree with a trivial flake (nixpkgs from the local registry's path) whose dev shell sets SWARM_DEVSHELL. -/
def devFlake (t : T) : IO Bool := do
  let sys := strip (← t.exec ["nix", "eval", "--impure", "--raw", "--expr", "builtins.currentSystem"]).stdout
  let np := strip (← t.exec ["nix", "eval", "--raw", "nixpkgs#path"]).stdout
  if sys == "" || np == "" then return false
  put (t.wt ++ "/flake.nix") ("{\n  inputs.nixpkgs.url = \"path:" ++ np ++ "\";\n  outputs = { self, nixpkgs }: {\n    devShells." ++ sys ++
    ".default = nixpkgs.legacyPackages." ++ sys ++ ".mkShell { SWARM_DEVSHELL = \"yes\"; };\n  };\n}\n")
  discard <| t.exec ["git", "-C", t.wt, "add", "-A"]
  return true

def test_run_enters_the_dev_shell (t : T) : IO Unit := do
  if (← t.exec ["sh", "-c", "command -v nix"]).code != 0 then return  -- skipped: no nix
  unless ← devFlake t do return
  let cmd := "echo dev=$SWARM_DEVSHELL"
  let o : Opts := { env := [("IN_NIX_SHELL", none)] }  -- a suite run inside a nix shell (swarm run on Linux)
  has (← t.sw "b" ["run", "--", cmd] o).stdout "dev=yes"
  has (← t.sw "b" ["run", "--", cmd] o).stdout "dev=yes"  -- the cached profile
  has (← t.sw "b" ["run", "--no-devshell", "--", cmd] o).stdout "dev=\n"
  mkdir (t.wt ++ "/.claude")
  put (t.wt ++ "/.claude/swarm.json") (json% {"run": {"devshell": false}}).compress
  has (← t.sw "b" ["run", "--", cmd] o).stdout "dev=\n"
  put (t.wt ++ "/.claude/swarm.json") "{}"
  -- a shell that does not build ends the job with the hint
  put (t.wt ++ "/flake.nix") "{ outputs = { self }: throw \"broken shell\"; }\n"
  discard <| t.exec ["git", "-C", t.wt, "add", "-A"]
  let r ← t.sw "b" ["run", "--", cmd] { o with ok := false }
  eq r.code 1
  has r.stdout "the dev shell did not build; --no-devshell runs without it"

def test_run_note_state_and_cleanup (t : T) : IO Unit := do
  let home ← fakeRemote t
  let hclog := t.d ++ "/hc.log"
  let pr ← fakeProc t
  t.agent "a"
  let n ← now t
  let n600 := n - 600; let n120 := n - 120
  t.q_ "insert into meta(k, v) values('machines',?)" [.text (json% {
    "laptop": {"state": "connected", "ts": $n, "cores": 24, "load": 3.5, "avail_kb": 83886080, "total_kb": 97517568,
      "psi": 0},
    "nas": {"state": "disconnected", "ts": $n, "since": $n600}}).compress]
  let d := ".cache/swarm-run/repo/wt"
  let wtReal := strip (← t.exec ["realpath", t.wt]).stdout
  -- of the repo, as `swarm run` records it: the repo's sweep reads its own events
  t.q_ "insert into event(ts,agent,kind,path,data,repo) values(?,?,?,?,?,?)"
    [.int n120, "a", "job-start", "1", .text (json% {"machine": "laptop", "hc": "laptop/t9", "wt": $wtReal, "dir": $d,
      "cmd": "cargo test -p x", "pid": 999999999}).compress, .text t.repo]
  let out := (← swp t "a" pr ["machine"]).stdout
  has out "laptop: 80/93G available, load 3.5 on 24 cores, mem pressure 0%, jobs: a cargo test -p x 2m"
  has out "nas: disconnected since"
  let mut lost : Array Json := #[]
  for j in arr ((← parse (← t.sw "a" ["state", "--json"]).stdout).f "running") do
    if j.f "machine" != Json.null then lost := lost.push (toJson [j.f "machine", j.f "job", j.f "lost"])
  eq lost (json% [["laptop", "1", true]])  -- swarm run gone, terminal gone
  -- watchd's probe of each machine, only from a Herdr terminal
  t.sw_ "a" ["watchd", "--once"] { hc := some "t1", cwd := some t.repo }
  let lap := (← parse (((← t.q1 "select v from meta where k='machines'").f "v").s?.getD "")).f "laptop"
  eq (lap.f "state") "connected"
  unless (lap.f "cores").i > 0 do fail "cores"
  unless (lap.f "total_kb").i > 0 do fail "total_kb"
  -- a landed worktree's dirs go on every machine its jobs used
  mkdir (home ++ "/" ++ d ++ "/src")
  idle t "e" [("wt", t.wt)]
  t.made t.wt "e"
  commsTick t
  unless ← ended t "e" do fail "not ended"
  if subIn (← readF [hclog]) "rm -rf" then fail "ending an agent cleans nothing"
  let gd := strip (← t.git (some t.wt) ["rev-parse", "--absolute-git-dir"])
  for p in [t.wt, gd ++ "/logs/HEAD"] do discard <| t.exec ["touch", "-d", s!"@{(← now t) - 3600}", p]
  commsTick t  -- the sweep removes the worktree, then its remote dirs
  has (← readF [hclog]) s!"exec --on laptop --timeout 120 rm -rf {d}"
  if ← exists_ (home ++ "/" ++ d) then fail "remote dir still there"

def test_run_remote_job_telemetry (t : T) : IO Unit := do
  discard <| fakeRemote t
  let hclog := t.d ++ "/hc.log"
  t.agent "a"
  let n ← now t
  -- a process tree: sh and two sleeps
  let n3601 := n - 3601
  let pf := t.d ++ "/tree.pid"
  let treeArgs := #["-c", "echo $$ > " ++ shquote pf ++ "; exec sh -c 'sleep 30 & sleep 30 & wait' >/dev/null"]
  let tree ← IO.Process.spawn { cmd := "sh", args := treeArgs, stdin := .null, stdout := .null, stderr := .null }
  IO.sleep 300
  let pid := strip ((← slurp pf).getD "")
  t.defer do
    discard <| t.exec ["pkill", "-P", pid]; discard <| t.exec ["kill", pid]
    try discard tree.wait catch _ => pure ()
  put (t.d ++ "/get.t9") (json% {"state": "live", "pid": $pid.toNat!}).compress
  put (t.d ++ "/get.t7") (json% {"state": "exited"}).compress
  t.q_ "insert into meta(k, v) values('machines',?)"
    [.text (json% {"laptop": {"state": "connected", "ts": $n, "jobs": {"2": {"gone": $n3601}}}}).compress]
  for (id, hc, age) in [("1", "laptop/t9", 60), ("2", "laptop/t8", 9000), ("3", "laptop/t7", 30), ("4", "nas/t1", 30)] do
    let machine := (hc.splitOn "/").head!
    let jp : Nat := if id == "2" || id == "3" then 999999999 else pid.toNat!
    t.q_ "insert into event(ts,agent,kind,path,data) values(?,?,?,?,?)"
      [.int (n - age), "a", "job-start", .text id, .text (json% {"machine": $machine, "hc": $hc, "cmd": "cargo test",
        "pid": $jp}).compress]
  t.sw_ "a" ["watchd", "--once"] { hc := some "t1", cwd := some t.repo }
  has (← readF [hclog]) "sh t7 t8 t9\n"  -- one exec carries the job terminals, named as the machine names them
  let ms ← parse (((← t.q1 "select v from meta where k='machines'").f "v").s?.getD "")
  let js := (ms.f "laptop").f "jobs"
  unless ((js.f "1").f "rss_kb").i > 0 do fail "no rss_kb"  -- sh and both sleeps
  eq (js.f "2") (json% {"gone": $n3601}); eq (js.f "3") (Json.mkObj [("gone", (js.f "3").f "gone")])
  let mut exits : Array Json := #[]
  for row in ← t.q "select data from event where kind='job-end'" do
    exits := exits.push ((← parse ((row.f "data").s?.getD "")).f "exit")
  eq exits (json% ["lost", "lost"])  -- job 2: gone over an hour; job 3: its submitter's pid is dead (board #212)
  has (((← t.q1 "select data from event where kind='job-end' and path='3'").f "data").s?.getD "") "submitter gone"
  has (← readF [hclog]) "kill laptop/t7"
  let ms := ms.setObjVal! "nas" (json% {"state": "disconnected", "ts": $n, "since": $n})
  t.q_ "update meta set v=? where k='machines'" [.text ms.compress]
  let running := (arr ((← parse (← t.sw "a" ["state", "--json"]).stdout).f "running")).filter (·.f "machine" != Json.null)
  let ids := (running.map fun j => (j.f "job").s?.getD "").qsort (· < ·)
  eq ids (json% ["1", "4"])
  let run (id : String) : Json := (running.find? fun j => (j.f "job").s? == some id).getD .null
  eq (toJson [(run "1").f "lost", (run "1").f "rss_kb"]) (toJson [Json.bool false, (js.f "1").f "rss_kb"])
  eq (toJson [(run "4").f "unreachable", (run "4").f "lost"]) (json% [true, false])
  has (← t.sw "a" ["machine"]).stdout " cargo test 1m 0.0G"

def tests : List Case := [
  ("test_one_watchd", test_one_watchd),
  ("test_one_watchd_serves_every_swarm", test_one_watchd_serves_every_swarm),
  ("test_watchd_leaves_another_swarms_claim", test_watchd_leaves_another_swarms_claim),
  ("test_machine_note_and_patterns", test_machine_note_and_patterns),
  ("test_pressure_edge_oom_and_orphans", test_pressure_edge_oom_and_orphans),
  ("test_machine_line_at_decisions", test_machine_line_at_decisions),
  ("test_pressure_notice_reaches_stayers", test_pressure_notice_reaches_stayers),
  ("test_ci_red_is_one_task_closed_on_green", test_ci_red_is_one_task_closed_on_green),
  ("test_ci_acts_only_on_the_repos_tasks", test_ci_acts_only_on_the_repos_tasks),
  ("test_run_remote_syncs_runs_and_brings_back", test_run_remote_syncs_runs_and_brings_back),
  ("test_run_never_ran_or_lost_is_255", test_run_never_ran_or_lost_is_255),
  ("test_run_local_records_job", test_run_local_records_job),
  ("test_run_enters_the_dev_shell", test_run_enters_the_dev_shell),
  ("test_run_note_state_and_cleanup", test_run_note_state_and_cleanup),
  ("test_run_remote_job_telemetry", test_run_remote_job_telemetry)]

end SwarmLean.Tests.Cli.WatchdRun
