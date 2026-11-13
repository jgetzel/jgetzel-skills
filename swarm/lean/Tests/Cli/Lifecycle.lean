import Tests.Cli.Fixture

/-! cli_lifecycle_spec.lua: join/leave, locks, sweep, landed agents, digests, CI, block/unblock, task deps. -/

namespace SwarmLean.Tests.Cli.Lifecycle
open SwarmLean.Tests.Cli
open SwarmLean.Sqlite (Val)
open Lean (Json toJson)

def now : IO Int := return (← Shim.nowF).toUInt64.toNat
/-- OLD: an hour ago. -/
def old : IO Int := return (← now) - 3600
def ok (b : Bool) (msg := "assertion failed") : IO Unit := unless b do fail msg
def exists_ (p : String) : IO Bool := (p : System.FilePath).pathExists
def rmtree (p : String) : IO Unit := discard <| IO.Process.output { cmd := "rm", args := #["-rf", p] }
def mkdirp (p : String) : IO Unit := IO.FS.createDirAll p
def touch (p : String) (at_ : Option Int := none) : IO Unit :=
  discard <| IO.Process.output { cmd := "touch", args := match at_ with | some n => #["-d", s!"@{n}", p] | none => #[p] }
def count (s sub : String) : Nat := (s.splitOn sub).length - 1
def state (t : T) : IO Json := do
  return (Json.parse (← t.sw "a" ["state", "--json"]).stdout).toOption.getD .null
def swp (pr : String) : Opts := { env := [("SWARM_PROC", some pr)] }

def commsTick (t : T) : IO Unit :=
  t.sw_ "a" ["watchd", "--once", "--comms", "comms", "--max-agents", "0"]
def idle (t : T) (name : String) (kw : List (String × Val) := []) : IO Unit := do
  let o : List (String × Val) :=
    [("status", "idle"), ("last_active", .int (← old)), ("waiter", .int (← IO.Process.getPID).toNat)]  -- a live waiter
  t.agent name (o.filter (fun (k, _) => !kw.any (·.1 == k)) ++ kw)
def ended (t : T) (name : String) : IO Bool :=
  return (← t.q1 "select ended from agent where name=?" [.text name]).f "ended" != .null
def branches (t : T) : IO String := t.git t.repo ["branch", "--list", "w2"]
def commitWip (t : T) (name : String) : IO Unit := do
  t.write "b" name "wip"
  discard <| t.git t.wt ["add", "."]
  discard <| t.git t.wt ["commit", "-qm", "wip"]
/-- Same content, different commits, on w2 and main. -/
def squash (t : T) : IO Unit := do
  for who in ["b", "a"] do
    t.write who "a.txt" "squashed"
    discard <| t.git (← t.cwdOf who) ["commit", "-qam", "change"]
def oldWt (t : T) (path : String) : IO Unit := do
  let gd := strip (← t.git path ["rev-parse", "--absolute-git-dir"])
  for p in [path, gd ++ "/logs/HEAD"] do touch p (some (← old))

def fakeProc (t : T) : IO String := do
  let r := t.d ++ "/proc"
  mkdirp (r ++ "/pressure")
  put (r ++ "/uptime") "10000.0 0\n"
  put (r ++ "/meminfo") "MemTotal: 32000000 kB\nMemAvailable: 20000000 kB\n"
  for k in ["memory", "cpu"] do put (r ++ "/pressure/" ++ k) "some avg10=1.0 avg60=0 avg300=0 total=0\n"
  -- machine.procs() reads the fixture
  discard <| t.fake "ps" "#!/bin/sh\ncat \"$SWARM_PROC\"/[0-9]*/ps 2>/dev/null; exit 0\n"
  return r
def addProc (r : String) (pid ppid : Nat) (comm : String) (argv : List String) (cwd : Option String := none) : IO Unit := do
  let d := s!"{r}/{pid}"
  mkdirp d
  let f := ["S", toString ppid] ++ List.replicate 17 "0" ++ [toString ((10000 - 240) * 100), "0", "0"]  -- starttime (CLK_TCK 100), vsize, rss
  put (d ++ "/stat") s!"{pid} ({comm}) {" ".intercalate f}"
  put (d ++ "/cmdline") ("\u0000".intercalate argv ++ "\u0000")
  put (d ++ "/oom_score_adj") "0"
  put (d ++ "/ps") s!"{pid} {ppid} 0 4:00 0:00 {" ".intercalate argv}\n"
  if let some c := cwd then discard <| IO.Process.output { cmd := "ln", args := #["-s", c, d ++ "/cwd"] }

-- ---- join, leave, who ----
def test_join_leave_who (t : T) : IO Unit := do
  t.liveHc ["t1", "t2"]
  t.sw_ "x" ["join"]
  t.q_ "insert into msg(ts,frm,dest,body) values(0,'x','@all','older run')"
  t.sw_ "a" ["join"] { hc := some "t1" }
  eq ((← t.q1 "select last_msg_id n from cursor where agent='a'").f "n") 1  -- skips older broadcasts
  has (← t.sw "a" ["join"] { hc := some "t2", ok := false }).stderr "a is bound to t1; this terminal is t2. `swarm join --takeover`"
  t.sw_ "a" ["join", "--takeover", "--model", "opus"] { hc := some "t2" }
  let a ← t.q1 "select hc, model from agent where name='a'"
  eq [a.f "hc", a.f "model"] ["t2", "opus"]
  eq ((← t.q1 "select data from event where kind='takeover'").f "data") "t1 -> t2"
  eq (← t.sw "a" ["join", "p", "q"] { ok := false }).code 2  -- bad usage
  t.sw_ "b" ["join"]
  t.q_ "insert into lock(path,agent,since,lease_until) values('x.txt','b',0,9999999999)"
  t.q_ "insert into task(title,state,owner,lease_until) values('t','claimed','b',9999999999)"
  t.q_ "update agent set ctx_tokens=52000 where name='b'"
  let who := (← t.sw "x" ["who"]).stdout
  has who "machine: "
  has (splitlines who) "b idle ctx=52k idle=0m cache=warm wt: ? locks: x.txt"
  t.sw_ "x" ["leave", "b"]
  let b ← t.q1 "select status, ended is not null e from agent where name='b'"
  eq [b.f "status", b.f "e"] (json% ["ended", 1])
  let tk ← t.q1 "select state, owner from task"
  eq [tk.f "state", tk.f "owner", toJson (← t.q "select * from lock")] (json% ["open", null, []])
  hasnt (← t.sw "x" ["who"]).stdout "\nb "
  has (← t.sw "b" ["leave"] { ok := false }).stderr "b was ended at"  -- fenced
  t.sw_ "b" ["join"]
  let b ← t.q1 "select status, ended from agent where name='b'"
  eq [b.f "status", b.f "ended"] (json% ["idle", null])
  let kinds := (← t.q "select kind from event where agent='b'").map (·.f "kind")
  eq kinds ["join", "leave", "join"]

def test_who_flags_stale_herdr_copies (t : T) : IO Unit := do
  let home := strip (← t.exec ["mktemp", "-d", s!"{(← IO.getEnv "TMPDIR").getD "/tmp"}/swarm-home-XXXXXX"]).stdout
  t.defer (rmtree home)
  mkdirp (home ++ "/mods/jgetzel-tabs")
  let run : IO String := return (← t.sw "x" ["who"] { env := [("HERDR_APP_HOME", some home)] }).stdout
  has (← run) "out of date: run install.sh"
  let stamp := ((← t.exec ["sh", "-c", "cat install.lua calendar/* ../swarm/herdr/mods/swarm/swarm.svg | sha256sum"]
    { cwd := (← swarmDir) ++ "/../herdr-mods" }).stdout.splitOn " ").head!
  put (home ++ "/jgetzel-install.stamp") (stamp ++ "\n")
  hasnt (← run) "out of date"

def test_branch_fallback_for_wt (t : T) : IO Unit := do
  t.agent "w2"; t.q_ "update agent set wt=null"
  discard <| t.git t.wt ["branch", "-m", "w2", "w2/x"]
  has (← t.sw "w2" ["who"]).stdout "wt: wt"

-- ---- locks ----
def test_lock_prefix_and_overlap (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "a" ["lock", "migrations/0070*"]
  eq ((← t.edit "b" "migrations/0070_x.sql").f "permissionDecision") "deny"
  t.sw_ "a" ["lock", "docs/"]
  eq ((← t.edit "b" "docs/x/y.md").f "permissionDecision") "deny"
  ok ((← t.sw "b" ["lock", "docs/x.md"] { ok := false }).code != 0)
  ok ((← t.sw "b" ["lock", "migrations/0070_a.sql"] { ok := false }).code != 0)
  t.sw_ "b" ["lock", "other/"]
  -- two globs neither of which covers the other can still share a file: m/a.lua (swarm/model: locksDisjoint)
  t.sw_ "a" ["lock", "m/*.lua"]
  ok ((← t.sw "b" ["lock", "m/a*"] { ok := false }).code != 0)
  t.sw_ "b" ["lock", "m/*.txt"]  -- no file ends in both .lua and .txt

def test_lock_released_when_work_lands (t : T) : IO Unit := do
  t.agent "a"
  discard <| t.edit "a" "a.txt"
  t.sw_ "a" ["lock", "a.txt"]
  t.tick
  eq (← t.q "select * from lock").size 1  -- no change yet: not seen
  t.write "a" "a.txt" "changed"
  t.tick
  eq ((← t.q1 "select seen from lock").f "seen") 1
  discard <| t.git t.repo ["commit", "-qam", "land"]
  discard <| t.exec ["git", "worktree", "prune"] { cwd := t.repo }
  t.tick  -- main moved to include the change: the file left a's working set
  eq (← t.q "select * from lock") (json% [])

def test_bash_lock_violation (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  discard <| t.edit "b" "b.txt"
  t.sw_ "a" ["lock", "a.txt"]
  t.write "b" "a.txt" "sneaky"
  t.tick
  has (← t.sw "b" ["read"]).stdout "violation"
  has (← t.sw "a" ["read"]).stdout "locked path"

def test_hard_lock_deny (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  t.sw_ "a" ["lock", "*.txt", "--reason", "refactor"]
  let out ← t.edit "b" "a.txt"
  eq (out.f "permissionDecision") "deny"
  has (out.f "permissionDecisionReason") "locked by a"
  has (out.f "permissionDecisionReason") "swarm post a"
  eq (← t.edit "a" "a.txt") (json% {})
  t.sw_ "a" ["unlock", "*.txt"]
  eq ((← t.edit "b" "a.txt").f "permissionDecision") Json.null

-- A lock typed in a subdirectory, or with ./, is the repo-relative path the edit hook sees.
def test_lock_path_is_repo_relative (t : T) : IO Unit := do
  t.agent "a"; t.agent "b"
  let sub := (← t.cwdOf "a") ++ "/sub"
  mkdirp sub
  has (← t.sw "a" ["lock", "x.txt"] { cwd := some sub }).stdout "locked sub/x.txt"
  eq ((← t.edit "b" "sub/x.txt").f "permissionDecision") "deny"
  t.sw_ "a" ["unlock", "./x.txt"] { cwd := some sub }
  eq ((← t.edit "b" "sub/x.txt").f "permissionDecision") Json.null
  t.sw_ "a" ["lock", "app/[id]/page.tsx"]  -- glob characters in a literal path still cover that path
  eq ((← t.edit "b" "app/[id]/page.tsx").f "permissionDecision") "deny"

-- ---- sweep ----
def test_sweep (t : T) : IO Unit := do
  oldWt t t.wt
  let pr ← fakeProc t
  let sweep : IO Unit := t.sw_ "a" ["watchd", "--once", "--comms", "comms", "--max-agents", "0"] (swp pr)
  has (← t.sw "a" ["watchd", "--dry-run"] (swp pr)).stdout t.wt
  ok (← exists_ t.wt)
  addProc pr 500 1 "bash" ["bash"] (some t.wt)
  sweep; ok (← exists_ t.wt) "a process is in it"
  rmtree (pr ++ "/500")
  t.agent "x" [("cwd", .text (t.wt ++ "/sub"))]
  sweep; ok (← exists_ t.wt) "a live agent's cwd is in it"
  t.q_ "update agent set ended=1 where name='x'"
  t.write "b" "new.txt" "wip"
  oldWt t t.wt
  sweep; ok (← exists_ t.wt) "dirty"
  IO.FS.removeFile (t.wt ++ "/new.txt")
  commitWip t "u.txt"
  oldWt t t.wt
  sweep; ok (← exists_ t.wt) "unlanded"
  discard <| t.git t.repo ["merge", "-q", "w2"]
  touch t.wt
  sweep; ok (← exists_ t.wt) "touched just now"
  oldWt t t.wt
  sweep
  ok (!(← exists_ t.wt)); eq (← branches t) ""
  eq ((← t.q1 "select count(*) n from event where kind='sweep'").f "n") 1
  has ((← t.q1 "select body from msg where kind='notice'").f "body") "swept 1"

def test_sweep_caches_not_landed (t : T) : IO Unit := do
  commitWip t "u.txt"
  oldWt t t.wt
  t.fakes; t.setGh "pr" (some "[]")
  let asked : IO Nat := return (← t.calls "gh").filter (·.startsWith "pr list") |>.length
  let ticks : IO Nat := return (← t.calls "hc").filter (·.startsWith "ls") |>.length
  let tick (n : Nat) : IO Unit := do  -- n more ticks of the running watchd
    let goal := (← ticks) + n
    for _ in [0:200] do
      if (← ticks) ≥ goal then return
      IO.sleep 100
    fail "watchd did not tick"
  -- the verdict cache lives in the daemon: run it, not --once
  let fb := (← t.fakebin).getD ""
  discard <| t.exec ["sh", "-c", "\"$0\" watchd --comms comms --max-agents 0 --interval 1 >/dev/null 2>&1 </dev/null & echo $!",
    ← swarmBin] { cwd := t.repo, env := [("SWARM_DB", some t.db), ("SWARM_NAME", some "a"), ("SWARM_PROC", some (← fakeProc t)),
      ("PATH", some (fb ++ ":" ++ (← basePath))), ("HC_TERMINAL_ID", none)], stdoutFile := some (t.d ++ "/watchd.pid") }
  let pid := strip ((← slurp (t.d ++ "/watchd.pid")).getD "")
  t.defer (discard <| t.exec ["sh", "-c", "kill $0 2>/dev/null", pid])
  tick 1; tick 1; eq (← asked) 1  -- unchanged: asked once over two ticks
  discard <| t.git t.repo ["commit", "-q", "--allow-empty", "-m", "x"]
  let noOrigin := if (← t.exec ["git", "-C", t.repo, "remote", "get-url", "origin"]).code != 0 then 1 else 0
  tick 2; eq (← asked) (1 + noOrigin)  -- B moved only when it is local main
  discard <| t.git t.wt ["commit", "-q", "--allow-empty", "-m", "y"]
  oldWt t t.wt
  let n ← asked; tick 2; eq (← asked) (n + 1)  -- HEAD moved

-- ---- landed agents ----
def test_landed_agent_ended_and_cleaned (t : T) : IO Unit := do
  idle t "e" [("wt", t.wt)]
  touch t.wt
  commsTick t
  ok (← ended t "e")
  ok ((← exists_ t.wt) && (← branches t) != "") "ending an agent removes no worktree or branch"
  oldWt t t.wt
  commsTick t  -- workspace GC: nobody attached now
  ok (!(← exists_ t.wt))
  eq (← branches t) ""
  eq ((← t.q1 "select data from event where kind='end'").f "data") "landed"

-- workspace GC removes the worktree of a base but never the base branch
def test_sweep_keeps_a_checked_out_base (t : T) : IO Unit := do
  discard <| t.git t.wt ["checkout", "-q", "-B", "formal"]
  t.sw_ "a" ["task", "add", "t", "--base", "formal"]
  oldWt t t.wt
  commsTick t
  ok (!(← exists_ t.wt))
  eq ((← t.git t.repo ["branch", "--list", "formal"]) != "") true

-- `swarm end`: the communicator only; checks unless --force; the worktree stays
def test_swarm_end (t : T) : IO Unit := do
  t.fakes
  t.agent "comms" [("status", "idle")]
  t.q_ "insert or replace into meta(k,v) values('comms','comms')"
  idle t "e" [("wt", t.wt)]
  t.sw_ "a" ["task", "add", "x"]; t.sw_ "e" ["task", "claim", "1"]
  eq (← t.sw "e" ["end", "e"] { ok := false }).code 1  -- not the communicator
  let r ← t.sw "comms" ["end", "e"] { ok := false }
  has r.stderr "owns a claimed task"
  ok (!(← ended t "e"))
  t.sw_ "comms" ["end", "e", "--force"]
  ok (← ended t "e")
  eq ((← t.q1 "select data from event where kind='end'").f "data") "forced by comms"
  ok (← exists_ t.wt)

-- another swarm's communicator that joined this board (a waiter it once ran here) is not ended (#117): its
-- terminal's cwd is outside this repo and its worktrees. A name ending in comms is nothing special (sw-roles §5).
def test_foreign_comms_not_ended (t : T) : IO Unit := do
  t.fakes
  t.setHc [json% {"address": "t1", "status": "idle", "cwd": $(t.d)}, json% {"address": "t2", "status": "idle", "cwd": $(t.wt)},
    json% {"address": "t3", "status": "idle"}]
  idle t "other-comms" [("wt", .text (t.wt ++ "-gone")), ("hc", "t1")]
  idle t "x-comms" [("wt", .text (t.wt ++ "-gone")), ("hc", "t2")]
  idle t "e" [("wt", .text (t.wt ++ "-gone")), ("hc", "t3")]  -- hc reports no cwd: judged as before
  commsTick t
  ok (!(← ended t "other-comms"))
  ok (← ended t "x-comms") "a *comms name still spared"
  ok (← ended t "e")

-- the communicator is a stayer: watchd's start gives it a stay, logged once, kept if it already has one
def test_watchd_makes_comms_a_stayer (t : T) : IO Unit := do
  idle t "comms"
  commsTick t; commsTick t
  eq ((← t.q1 "select stay from agent where name='comms'").f "stay") "the user's channel"
  eq (← t.q "select 1 x from event where kind='stay' and agent='comms'").size 1
  ok (!(← ended t "comms"))
  t.sw_ "comms" ["stay", "the user and the PR queue"]
  commsTick t
  eq ((← t.q1 "select stay from agent where name='comms'").f "stay") "the user and the PR queue"

--CHUNK2--

def tests : List Case := [
  ("test_join_leave_who", test_join_leave_who),
  ("test_who_flags_stale_herdr_copies", test_who_flags_stale_herdr_copies),
  ("test_branch_fallback_for_wt", test_branch_fallback_for_wt),
  ("test_lock_prefix_and_overlap", test_lock_prefix_and_overlap),
  ("test_lock_released_when_work_lands", test_lock_released_when_work_lands),
  ("test_bash_lock_violation", test_bash_lock_violation),
  ("test_hard_lock_deny", test_hard_lock_deny),
  ("test_lock_path_is_repo_relative", test_lock_path_is_repo_relative),
  ("test_sweep", test_sweep),
  ("test_sweep_caches_not_landed", test_sweep_caches_not_landed),
  ("test_landed_agent_ended_and_cleaned", test_landed_agent_ended_and_cleaned),
  ("test_sweep_keeps_a_checked_out_base", test_sweep_keeps_a_checked_out_base),
  ("test_swarm_end", test_swarm_end),
  ("test_foreign_comms_not_ended", test_foreign_comms_not_ended),
  ("test_watchd_makes_comms_a_stayer", test_watchd_makes_comms_a_stayer)]

end SwarmLean.Tests.Cli.Lifecycle
