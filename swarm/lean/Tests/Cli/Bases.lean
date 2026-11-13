import Tests.Cli.Fixture
import SwarmLean.Lib.Workspaces

/-! cli_bases_spec.lua: per-task bases (sw-bases, board #3): base_for, .claude/swarm.json base, task add --base, and
the checks that used to say main: lifecycle's landed check, the sweep, the conflict snapshot, CI; swarm-created
worktrees and the workspace table (board #5). -/

namespace SwarmLean.Tests.Cli.Bases
open SwarmLean.Tests.Cli
open Lean (Json toJson)
open SwarmLean.Sqlite (Val)

/-- Epoch seconds. -/
def now (t : T) : IO Int := return (strip (← t.exec ["date", "+%s"]).stdout).toInt!

def exists_ (p : String) : IO Bool := (p : System.FilePath).pathExists

def ended (t : T) (name : String) : IO Bool := do
  return (← t.q1 "select ended from agent where name=?" [.text name]).f "ended" != .null

def commsTick (t : T) : IO Unit := t.sw_ "a" ["watchd", "--once", "--comms", "comms", "--max-agents", "0"]

def idle (t : T) (name : String) (kw : List (String × Val) := []) : IO Unit := do
  let old := (← now t) - 3600
  let pid := Int.ofNat (← IO.Process.getPID).toNat
  let dflt : List (String × Val) := [("status", "idle"), ("last_active", .int old), ("waiter", .int pid)]
  t.agent name (dflt.filter (fun (k, _) => !kw.any (·.1 == k)) ++ kw)

/-- Sets atime and mtime of the worktree and its git log to an hour ago. -/
def oldWt (t : T) (path : String) : IO Unit := do
  let gd := strip (← t.git (some path) ["rev-parse", "--absolute-git-dir"])
  let old := (← now t) - 3600
  for p in [path, gd ++ "/logs/HEAD"] do discard <| t.exec ["touch", "-d", s!"@{old}", p]

-- w2 gets a commit and main fast-forwards to it; `formal` stays where main was
def landOnMainOnly (t : T) : IO Unit := do
  discard <| t.git t.repo ["branch", "formal"]
  t.write "b" "new.txt" "wip"
  discard <| t.git t.wt ["add", "."]
  discard <| t.git t.wt ["commit", "-qm", "wip"]
  discard <| t.git t.repo ["merge", "-q", "--ff-only", "w2"]

def doneTask (t : T) (owner base : String) : IO Unit := do
  t.sw_ "a" ["task", "add", "t", "--base", base]
  t.q_ "update task set state='done', owner=?, evidence='x' where id=1" [.text owner]

/-- An action of the real monad, run as the Lua called its module (the cwd, SWARM_DB as the Lua had them). -/
def runApp (act : App α) : IO α := do
  match ← (act.run.run { conn := ← IO.mkRef none }) with
  | .ok a => pure a
  | .error _ => fail "App action exited"

def claudeDir (t : T) : IO Unit := IO.FS.createDirAll (t.repo ++ "/.claude")

def test_base_for_task_then_repo_then_main (t : T) : IO Unit := do
  let r := some t.repo
  eq (← runApp (SwarmLean.Bases.default r : App String)) "main"
  eq (← runApp (SwarmLean.Bases.baseFor none r : App String)) "main"
  claudeDir t
  put (t.repo ++ "/.claude/swarm.json") "{\"base\": \"formal\"}"
  eq (← runApp (SwarmLean.Bases.default r : App String)) "formal"
  eq (← runApp (SwarmLean.Bases.baseFor none r : App String)) "formal"
  eq (← runApp (SwarmLean.Bases.baseFor (some "dev") r : App String)) "dev"
  put (t.repo ++ "/.claude/swarm.json") "{\"ci\": {}}"  -- no base key
  eq (← runApp (SwarmLean.Bases.default r : App String)) "main"

def test_task_add_base_stored_and_shown (t : T) : IO Unit := do
  t.sw_ "a" ["task", "add", "plain"]
  t.sw_ "a" ["task", "add", "on formal", "--base", "formal"]
  eq ((← t.q1 "select base from task where id=1").f "base") Json.null
  eq ((← t.q1 "select base from task where id=2").f "base") "formal"
  hasnt (← t.sw "a" ["task", "show", "1"]).stdout "base:"
  has (← t.sw "a" ["task", "show", "2"]).stdout "base: formal"

def test_ref_prefers_the_remote_branch (t : T) : IO Unit := do
  let r := some t.repo
  eq (← runApp (SwarmLean.Bases.ref "main" r : App String)) "main"  -- no origin
  discard <| t.git t.repo ["update-ref", "refs/remotes/origin/main", "HEAD"]
  eq (← runApp (SwarmLean.Bases.ref "main" r : App String)) "origin/main"
  eq (← runApp (SwarmLean.Bases.ref "formal" r : App String)) "formal"  -- origin lacks it

-- lifecycle: an agent whose task is on `formal` is not done while its work is only on main
def test_agent_kept_until_work_is_on_its_tasks_base (t : T) : IO Unit := do
  landOnMainOnly t
  idle t "e" [("wt", t.wt)]
  doneTask t "e" "formal"
  commsTick t
  if ← ended t "e" then fail "on main, not on formal"
  unless ← exists_ t.wt do fail "worktree gone"
  discard <| t.git t.repo ["branch", "-f", "formal", "w2"]
  commsTick t
  unless ← ended t "e" do fail "not ended"

def test_agent_without_task_uses_the_repo_base (t : T) : IO Unit := do
  landOnMainOnly t
  idle t "e" [("wt", t.wt)]
  claudeDir t
  put (t.repo ++ "/.claude/swarm.json") "{\"base\": \"formal\"}"
  commsTick t
  if ← ended t "e" then fail "the repo's base is formal"
  discard <| t.git t.repo ["branch", "-f", "formal", "w2"]
  commsTick t
  unless ← ended t "e" do fail "not ended"

def test_agent_on_main_task_still_ended_on_main (t : T) : IO Unit := do
  landOnMainOnly t
  idle t "e" [("wt", t.wt)]
  doneTask t "e" "main"
  commsTick t
  unless ← ended t "e" do fail "not ended"

-- the sweep protects every base a task names, and main
def test_sweep_removes_work_landed_on_a_task_base (t : T) : IO Unit := do
  discard <| t.git t.repo ["branch", "formal"]
  t.write "b" "new.txt" "wip"
  discard <| t.git t.wt ["add", "."]
  discard <| t.git t.wt ["commit", "-qm", "wip"]
  discard <| t.git t.repo ["branch", "-f", "formal", "w2"]  -- on formal only
  oldWt t t.wt
  t.fakes
  commsTick t
  unless ← exists_ t.wt do fail "no task names formal: not landed"
  t.sw_ "a" ["task", "add", "t", "--base", "formal"]
  commsTick t
  if ← exists_ t.wt then fail "formal is a base now"

-- the conflict snapshot: work for different bases can't meet
def test_conflict_only_between_agents_on_the_same_base (t : T) : IO Unit := do
  discard <| t.git t.repo ["branch", "formal"]
  t.agent "a"; t.agent "b"
  t.sw_ "a" ["task", "add", "t", "--base", "formal"]
  t.sw_ "b" ["task", "claim", "1"]
  discard <| t.edit "a" "a.txt"; discard <| t.edit "b" "a.txt"
  t.write "a" "a.txt" "y"; t.write "b" "a.txt" "z"
  t.tick
  eq ((← t.q1 "select count(*) n from msg where kind='notice'").f "n") 0
  t.q_ "update task set state='open', owner=null where id=1"
  t.tick
  eq ((← t.q1 "select count(*) n from msg where kind='notice'").f "n") 2

-- CI follows the repo's base, and a base other than main that origin lacks has none
def test_ci_polls_only_a_base_with_a_remote (t : T) : IO Unit := do
  t.fakes
  t.agent "a"
  t.setGhJ "api" (json% [{"databaseId": 1, "headSha": "a1", "status": "completed", "conclusion": "success",
    "url": "u1", "createdAt": "2026-11-08T10:00:00Z", "updatedAt": "2026-11-08T10:03:00Z", "event": "push"}])
  claudeDir t
  put (t.repo ++ "/.claude/swarm.json") "{\"base\": \"formal\"}"
  t.sw_ "a" ["watchd", "--once", "--ci"]
  eq (← t.calls "gh").length 0 "formal is local only"
  discard <| t.git t.repo ["update-ref", "refs/remotes/origin/formal", "HEAD"]
  t.q_ "delete from meta where k='ci_polled'"
  t.sw_ "a" ["watchd", "--once", "--ci"]
  unless subIn ((← t.calls "gh").head?.getD "") "branch=formal" do fail "polls the repo's base"

-- ---- swarm-created worktrees and the workspace table (board #5) ----
def spawnOn (t : T) (base : String) : IO String := do
  t.fakes
  discard <| t.git t.repo ["branch", "formal"]
  t.sw_ "a" ["task", "add", "do it", "--base", base]
  t.sw_ "a" ["spawn", "t-9", "--model", "haiku", "--task", "1"]
  return t.d ++ "/repo-t-9"

def test_spawn_task_makes_and_records_the_worktree (t : T) : IO Unit := do
  let wt ← spawnOn t "formal"
  eq (strip (← t.git (some wt) ["rev-parse", "--abbrev-ref", "HEAD"])) "t-9/1"
  eq (strip (← t.git (some wt) ["rev-parse", "HEAD"])) (strip (← t.git t.repo ["rev-parse", "formal"]))
  let w ← t.q1 "select * from workspace"
  eq (toJson [w.f "path", w.f "branch", w.f "base", w.f "agent", w.f "ro"]) (json% [$wt, "t-9/1", "formal", "t-9", 0])
  let argv := match ((← t.launched)[0]!).f "argv" with | .arr a => a.toList.map (·.s?.getD "") | _ => []
  has (" ".intercalate argv) s!"Your worktree: {wt}"

def test_spawn_attach_links_read_only (t : T) : IO Unit := do
  let wt ← spawnOn t "main"
  t.sw_ "a" ["spawn", "t-8", "--model", "haiku", "--attach", wt, "--", "review"]
  let w ← t.q1 "select ro, branch from workspace where agent='t-8'"
  eq (toJson [w.f "ro", w.f "branch"]) (json% [1, "t-9/1"])
  has (← t.sw "a" ["spawn", "t-7", "--attach", t.d ++ "/nope", "--", "x"] { ok := false }).stderr "not a swarm workspace"

-- the Lua chdir'd to the repo for conflict.worktrees(); so does this (restored after)
def test_owned_wts_reads_the_table_not_names (t : T) : IO Unit := do
  let wt ← spawnOn t "main"
  discard <| t.git t.repo ["worktree", "add", "-q", "-b", "t-9/other", t.d ++ "/elsewhere"]
  let prev ← IO.currentDir
  t.defer (IO.Process.setCurrentDir prev)
  IO.Process.setCurrentDir t.repo
  SwarmLean.Shim.setenv "SWARM_DB" t.db
  let c ← SwarmLean.connect
  let db ← SwarmLean.loadDb c [.workspace]
  let wts ← runApp (SwarmLean.Workspaces.worktrees : App _)
  -- the heuristic would also take t-9/other
  eq (SwarmLean.Workspaces.ownedWts "t-9" wts (some db)) [wt]
  eq (SwarmLean.Workspaces.ownedWts "t-9" wts).length 2  -- an agent with no row falls back

def test_hook_denies_checking_out_a_base_and_watchd_flags_one (t : T) : IO Unit := do
  let wt ← spawnOn t "formal"
  t.setCwd "t-9" wt
  let bash (cmd : String) : Json := json% {"tool_name": "Bash", "tool_input": {"command": $cmd}}
  let out ← t.hook "t-9" "pre-tool" (bash "cd x && git checkout formal") (some "hc1")
  eq (out.f "permissionDecision") "deny"
  eq ((← t.hook "t-9" "pre-tool" (bash "git checkout -b feature") (some "hc1")).f "permissionDecision") Json.null
  eq ((← t.hook "t-9" "pre-tool" (bash "git checkout t-9/1") (some "hc1")).f "permissionDecision") Json.null
  discard <| t.git (some wt) ["checkout", "-q", "formal"]  -- it got past anyway
  commsTick t
  has ((← t.q1 "select count(*) n, group_concat(body) b from msg where dest='t-9'").f "b") "has formal checked out"

def tests : List Case := [
  ("test_base_for_task_then_repo_then_main", test_base_for_task_then_repo_then_main),
  ("test_task_add_base_stored_and_shown", test_task_add_base_stored_and_shown),
  ("test_ref_prefers_the_remote_branch", test_ref_prefers_the_remote_branch),
  ("test_agent_kept_until_work_is_on_its_tasks_base", test_agent_kept_until_work_is_on_its_tasks_base),
  ("test_agent_without_task_uses_the_repo_base", test_agent_without_task_uses_the_repo_base),
  ("test_agent_on_main_task_still_ended_on_main", test_agent_on_main_task_still_ended_on_main),
  ("test_sweep_removes_work_landed_on_a_task_base", test_sweep_removes_work_landed_on_a_task_base),
  ("test_conflict_only_between_agents_on_the_same_base", test_conflict_only_between_agents_on_the_same_base),
  ("test_ci_polls_only_a_base_with_a_remote", test_ci_polls_only_a_base_with_a_remote),
  ("test_spawn_task_makes_and_records_the_worktree", test_spawn_task_makes_and_records_the_worktree),
  ("test_spawn_attach_links_read_only", test_spawn_attach_links_read_only),
  ("test_owned_wts_reads_the_table_not_names", test_owned_wts_reads_the_table_not_names),
  ("test_hook_denies_checking_out_a_base_and_watchd_flags_one", test_hook_denies_checking_out_a_base_and_watchd_flags_one)]

end SwarmLean.Tests.Cli.Bases
