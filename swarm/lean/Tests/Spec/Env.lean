import Tests.Cli.Fixture
import SwarmLean.Cmd.Watchd
import SwarmLean.Cmd.Msgs

/-! env_spec.lua: each tool assumption of SwarmLean/Assumptions.lean against the real tool, in a scratch repo, through
the code's own calls where there is one. A case carries the name its assumption's tag gives; check.sh refuses a tag
with no case here or in sqlite_spec. The hc cases start terminals in your hc: they run only with SWARM_TEST_HC=1. The
gh cases ask GitHub about this repo's latest PRs: they run only with SWARM_TEST_GH=1. -/

namespace SwarmLean.Tests.Spec.Env
open SwarmLean SwarmLean.Tests.Cli

/-- Runs an App action. -/
def app (act : App α) : IO α := do
  match ← (act.run.run { conn := ← IO.mkRef none }) with
  | .ok a => pure a
  | .error e => fail s!"exit {e.code}"

/-- git in `cwd`, asserting success: its stdout, stripped. -/
def git (t : T) (cwd : String) (args : List String) : IO String := return strip (← t.git (some cwd) args)

/-- git's exit code. -/
def gx (t : T) (cwd : String) (args : List String) : IO Int := return (← t.exec (["git", "-C", cwd] ++ args)).code

/-- What a commit holds, in the assumptions' reading: its files, by content. -/
def files (t : T) (rev : String) : IO (List String) := return SwarmLean.splitlines (← git t t.repo ["ls-tree", "-r", rev])

def subset (a b : List String) : Bool := a.all b.contains

/-- The repo's durable state (Tools.SameRepo): worktrees with branch and HEAD, branch tips, commits, and each status. -/
def durable (t : T) : IO String := do
  let wl ← git t t.repo ["worktree", "list", "--porcelain"]
  let mut s := [wl, ← git t t.repo ["for-each-ref", "refs/heads"], ← git t t.repo ["rev-list", "--all"]]
  for l in SwarmLean.splitlines wl do
    if l.startsWith "worktree " then
      let p := (l.drop 9).toString
      s := s ++ [p ++ ":" ++ (← git t p ["status", "--porcelain"])]
  return "\n".intercalate s

/-- The worktrees `git worktree list --porcelain` run in `main` lists, real paths (the sweep's parse). -/
def listed (main : String) : IO (List String) := do
  let out := ((← outputIO ["git", "worktree", "list", "--porcelain"] (some main) []).filter (·.code == 0)).map (·.stdout)
  let mut r := []
  for l in SwarmLean.splitlines (out.getD "") do
    if l.startsWith "worktree " then
      let p := (l.drop 9).toString
      r := r ++ [← try pure (← IO.FS.realPath p).toString catch _ => pure p]
  return r

/-- The sweep's and landed's reading of status: clean when it prints nothing but space. -/
def clean (wt : String) : IO Bool := do
  return match ← outputIO ["git", "--no-optional-locks", "-C", wt, "status", "--porcelain"] none [] with
    | some o => o.code == 0 && strip o.stdout == ""
    | none => false

/-- No system or global git config, and a gh on PATH that finds no merged PR: only git's answers count. -/
def setup (t : T) : IO Unit := do
  Shim.setenv "GIT_CONFIG_NOSYSTEM" "1"; Shim.setenv "GIT_CONFIG_GLOBAL" "/dev/null"
  IO.FS.createDirAll (t.d ++ "/bin")
  put (t.d ++ "/bin/gh") "#!/bin/sh\nexit 1\n" "+x"
  Shim.setenv "PATH" s!"{t.d}/bin:{← basePath}"

/-- Worktrees e1, e2, e3 of the repo, on branches of their names, at main. -/
def addWts (t : T) : IO (List String) := do
  let ws := [1, 2, 3].map fun i => s!"{t.d}/e{i}"
  for (w, i) in ws.zip [1, 2, 3] do discard <| git t t.repo ["worktree", "add", "-q", "-b", s!"e{i}", w, "main"]
  return ws

-- ---------- ancestor_reach, same_content_reach ----------

/-- `k` is an ancestor of `t` by the recorded parents (`par[k]`, 0 for none). -/
def anc (par : Array Nat) (k t : Nat) : Bool := Id.run do
  let mut t := t
  for _ in [0:par.size] do
    if t == 0 then return false
    if t == k then return true
    t := par[t]!
  return false

/-- A random history: commits that each add a fresh file, squash merges, fast-forwards, on main and three branches.
The commits (1-based), each one's recorded parent, and each branch's tip. -/
def history (t : T) : IO (Array String × Array Nat × List (String × Nat)) := do
  let repo := t.repo
  let brs := ["main", "b1", "b2", "b3"]
  let mut sha := #["", ← git t repo ["rev-parse", "HEAD"]]
  let mut par := #[0, 0]
  let mut tip : List (String × Nat) := brs.map (·, 1)
  for b in brs.tail do discard <| git t repo ["branch", b]
  let tipOf (tip : List (String × Nat)) (b : String) : Nat := (tip.lookup b).getD 0
  let setTip (tip : List (String × Nat)) (b : String) (v : Nat) := tip.map fun (x, n) => (x, if x == b then v else n)
  let mut g := mkStdGen 34
  let mut squashes := 0
  for i in [1:25] do
    let (bi, g1) := randNat g 0 3
    let (si, g2) := randNat g1 0 3
    let (op, g3) := randNat g2 1 4
    g := g3
    let b := brs[bi]!
    let s := brs[si]!
    discard <| git t repo ["checkout", "-q", b]
    if op ≤ 2 || s == b then
      put s!"{repo}/f{i}" s!"patch {i}\n"
      discard <| git t repo ["add", "-A"]; discard <| git t repo ["commit", "-q", "-m", s!"c{i}"]
    else if op == 3 then
      discard <| git t repo ["merge", "-q", "--squash", s]
      if (← gx t repo ["diff", "--cached", "--quiet"]) == 0 then continue
      discard <| git t repo ["commit", "-q", "-m", s!"squash {s}"]
      squashes := squashes + 1
    else
      if (← gx t repo ["merge", "-q", "--ff-only", s]) != 0 then continue
      tip := setTip tip b (tipOf tip s)
      continue
    sha := sha.push (← git t repo ["rev-parse", "HEAD"])
    par := par.push (tipOf tip b)
    tip := setTip tip b (sha.size - 1)
  discard <| git t repo ["checkout", "-q", "--detach", "main"]
  if squashes == 0 then fail "the history has a squash merge"
  return (sha, par, tip)

/-- git's --is-ancestor is the recorded ancestry, and a branch holds its ancestors' files. -/
def ancestor_reach (t : T) : IO Unit := do
  setup t
  let (sha, par, tip) ← history t
  let mut yes := 0
  let mut no := 0
  for (b, tb) in tip do
    let bf ← files t b
    for k in [1:sha.size] do
      let ga := (← gx t t.repo ["merge-base", "--is-ancestor", sha[k]!, b]) == 0
      eq ga (anc par k tb) s!"ancestor_reach: git's --is-ancestor {k} {b} is ancestry"
      if ga then
        eq (subset (← files t sha[k]!) bf) true s!"ancestor_reach: {b} holds ancestor {k}'s files"
        yes := yes + 1
      else no := no + 1
  eq (yes > 0 && no > 0) true "ancestor_reach: the history has ancestors and not"

/-- What `Lifecycle.landedRef1` answers yes to, the branch holds the files of; some commits landed by a squash, some
did not land. -/
def same_content_reach (t : T) : IO Unit := do
  setup t
  let (sha, _, tip) ← history t
  let mut squash := 0
  let mut neither := 0
  for (b, _) in tip do
    let bf ← files t b
    for k in [1:sha.size] do
      let ga := (← gx t t.repo ["merge-base", "--is-ancestor", sha[k]!, b]) == 0
      let landed ← app (Lifecycle.landedRef1 t.repo sha[k]! b)
      if landed then eq (subset (← files t sha[k]!) bf) true s!"same_content_reach: landedRef1({k}, {b}) means {b} holds its files"
      if landed && !ga then squash := squash + 1
      if !landed then neither := neither + 1
  eq (squash > 0 && neither > 0) true "same_content_reach: the history has squash-landed and unlanded commits"

-- ---------- status_clean, listed_on, wt_remove, del_ref ----------

def status_clean (t : T) : IO Unit := do
  setup t
  let wt := t.wt
  eq (← clean wt) true "status_clean: a fresh worktree is clean"
  put s!"{wt}/new" "x\n"
  eq (← clean wt) false "status_clean: an untracked file is unclean"
  IO.FS.removeFile s!"{wt}/new"; IO.FS.createDirAll s!"{wt}/sub"; put s!"{wt}/sub/new" "x\n"
  eq (← clean wt) false "status_clean: an untracked file in a new directory is unclean"
  discard <| git t wt ["add", "-A"]; discard <| git t wt ["commit", "-q", "-m", "w"]
  eq (← clean wt) true "status_clean: committed is clean"
  put s!"{wt}/a.txt" "changed\n"
  eq (← clean wt) false "status_clean: a changed tracked file is unclean"
  discard <| git t wt ["checkout", "-q", "--", "a.txt"]
  eq (← clean wt) true "status_clean: restored is clean"

def listed_on (t : T) : IO Unit := do
  setup t
  let ws ← addWts t
  let l ← listed t.repo
  eq ((t.wt :: ws).all l.contains) true "listed_on: an added worktree is listed"
  discard <| git t t.repo ["worktree", "remove", ws[0]!]
  let l ← listed t.repo
  eq (l.contains ws[0]!) false "listed_on: a removed worktree is not listed"
  eq ((t.wt :: ws.tail).all l.contains) true "listed_on: the rest are"

def wt_remove (t : T) : IO Unit := do
  setup t
  let ws ← addWts t
  let (w1, w2, w3) := (ws[0]!, ws[1]!, ws[2]!)
  put s!"{w2}/untracked" "x\n"
  let before ← durable t
  eq ((← gx t t.repo ["worktree", "remove", w2]) != 0) true "wt_remove: a dirty worktree is refused"
  eq (← durable t) before "wt_remove: a refused remove changes nothing"
  eq (← System.FilePath.pathExists s!"{w2}/untracked") true "wt_remove: a refused remove keeps its files"
  let heads ← git t t.repo ["for-each-ref", "refs/heads"]
  let commits ← git t t.repo ["rev-list", "--all"]
  eq (← gx t t.repo ["worktree", "remove", w1]) 0 "wt_remove: a clean worktree is removed"
  eq (← System.FilePath.pathExists w1) false "wt_remove: its directory goes"
  eq (← git t t.repo ["for-each-ref", "refs/heads"]) heads "wt_remove: every branch (its own too) stays"
  eq (← git t t.repo ["rev-list", "--all"]) commits "wt_remove: every commit stays"
  eq (← git t w2 ["status", "--porcelain"]) "?? untracked" "wt_remove: other worktrees stay as they were"
  eq (← clean w3) true "wt_remove: other worktrees stay as they were"

/-- `Watchd.deleteBranch`: `branch -d` when merged into HEAD, else `update-ref -d` guarded by the tip the sweep checked. -/
def del_ref (t : T) : IO Unit := do
  setup t
  discard <| git t t.repo ["branch", "w1"]
  put s!"{t.wt}/w" "w\n"
  discard <| git t t.wt ["add", "-A"]; discard <| git t t.wt ["commit", "-q", "-m", "work"]
  let a ← git t t.repo ["rev-parse", "w1"]
  discard <| git t t.repo ["branch", "-f", "w1", "w2"]  -- w1 moved since the check, to work not in HEAD
  let refs ← git t t.repo ["for-each-ref", "refs/heads"]
  eq ((← gx t t.repo ["merge-base", "--is-ancestor", "w1", "HEAD"]) != 0) true
  app (Watchd.deleteBranch t.repo (some "w1") (some a) [])
  eq (← git t t.repo ["for-each-ref", "refs/heads"]) refs "del_ref: a branch that moved since the check is kept"
  app (Watchd.deleteBranch t.repo (some "main") (some (← git t t.repo ["rev-parse", "main"])) ["main"])
  eq (← git t t.repo ["for-each-ref", "refs/heads"]) refs "del_ref: a protected branch is kept"
  app (Watchd.deleteBranch t.repo (some "w1") (some (← git t t.repo ["rev-parse", "w1"])) [])
  eq ((← gx t t.repo ["rev-parse", "-q", "--verify", "refs/heads/w1"]) != 0) true "del_ref: the checked tip is deleted"
  eq (← git t t.repo ["for-each-ref", "refs/heads"])
    ("\n".intercalate ((SwarmLean.splitlines refs).filter (!·.endsWith "refs/heads/w1"))) "del_ref: no other branch goes"

-- ---------- touched_recent ----------

/-- The sweep's reading of when a worktree was last touched: its directory's and its git dir's logs/HEAD's mtime. -/
def lastTouched (t : T) (wt : String) : IO Int := do
  let gd ← git t wt ["rev-parse", "--absolute-git-dir"]
  let mut l := 0
  for p in [wt, joinPath (joinPath gd "logs") "HEAD"] do l := max l ((← app (Sys.mtime p : App _)).getD 0)
  return l

def recent (t : T) (wt : String) : IO Bool := return (← app (Clock.now : App Int)) - (← lastTouched t wt) < Watchd.SWEEP_IDLE

def touched_recent (t : T) : IO Unit := do
  setup t
  let wt := t.wt
  IO.FS.createDirAll s!"{wt}/sub"; put s!"{wt}/sub/x" "1\n"
  discard <| git t wt ["add", "-A"]; discard <| git t wt ["commit", "-q", "-m", "w"]
  eq (← recent t wt) true "touched_recent: a commit touches it"
  let stamp ← Shim.strftime "%Y%m%d%H%M.%S" (Int64.ofInt ((← app (Clock.now : App Int)) - 1860))
  for p in [wt, (← git t wt ["rev-parse", "--absolute-git-dir"]) ++ "/logs/HEAD"] do
    discard <| t.exec ["touch", "-t", stamp, p]
  eq (← recent t wt) false "touched_recent: 31 min untouched is not recent"
  put s!"{wt}/sub/x" "2\n"  -- the directory's mtime doesn't move for a nested file
  eq (← recent t wt) false "touched_recent: a nested edit leaves it not recent"
  eq (← clean wt) false "touched_recent: but unclean, so unswept"
  discard <| git t wt ["commit", "-q", "-am", "w again"]
  eq (← recent t wt) true "touched_recent: the commit touches logs/HEAD"

-- ---------- kill0_alive, cwds_proc ----------

/-- `sleep 30` with its cwd in `dir`. -/
def sleeper (dir : String) : IO (IO.Process.Child ⟨.null, .null, .null⟩) :=
  IO.Process.spawn { cmd := "sleep", args := #["30"], cwd := some dir, stdin := .null, stdout := .null, stderr := .null }

def kill0_alive (t : T) : IO Unit := do
  let c ← sleeper t.wt
  let pid : Int := c.pid.toNat
  eq (← app (Sys.pidAlive pid : App Bool)) true "kill0_alive: a live process answers kill 0"
  c.kill
  IO.sleep 1000
  eq (← app (Sys.pidAlive pid : App Bool)) true
    "kill0_alive: a zombie (dead, not yet reaped) still answers kill 0: alive means in the process table"
  discard <| c.wait
  eq (← app (Sys.pidAlive pid : App Bool)) false "kill0_alive: a reaped process doesn't"

def realOr (p : String) : IO String := try return (← IO.FS.realPath p).toString catch _ => return p

def cwds_proc (t : T) : IO Unit := do
  let c ← sleeper t.wt
  let pid : Int := c.pid.toNat
  IO.sleep 200
  let some cw ← app (Machine.cwds : App _) | fail "cwds_proc: Machine.cwds answers"
  let some d := cw.lookup pid | fail "cwds_proc: Machine.cwds lists the process"
  eq (Watchd.inside (← realOr d) t.wt) true "cwds_proc: a process in a worktree is seen inside it"
  c.kill; discard <| c.wait
  for (p, d) in (← app (Machine.cwds : App _)).getD [] do
    if Watchd.inside (← realOr d) t.wt then fail s!"cwds_proc: no process left inside, but {p}"

-- ---------- cgroup_kill_keeps ----------

/-- A process in a swarm-agent scope, in a worktree; "1" to the scope's `cgroup.kill` as `Lifecycle.endAgent` writes
it. Skipped where there is no systemd user scope. -/
def cgroup_kill_keeps (t : T) : IO Unit := do
  let name := s!"swarm-agent-env-{← IO.Process.getPID}.scope"
  let args := #["--user", "--scope", "--quiet", "--collect", s!"--unit={name}", "--", "sleep", "300"]
  let c ← IO.Process.spawn
    { cmd := "systemd-run", args, cwd := some t.wt, stdin := .null, stdout := .null, stderr := .null }
  let pid : Int := c.pid.toNat
  let mut cg := none
  for _ in [0:50] do
    -- until systemd moves it, the pid is in the caller's cgroup: an agent's own swarm-agent scope, never to be killed
    cg := (← app (Machine.cgroup pid : App _)).filter (·.dir.endsWith s!"/{name}")
    if cg.isSome then break
    IO.sleep 100
  let some g := cg
    | c.kill; discard <| c.wait; IO.eprintln "env_spec: cgroup_kill_keeps skipped (no systemd user scope here)"
  let d ← durable t
  IO.FS.writeFile (g.dir ++ "/cgroup.kill") "1"
  discard <| c.wait
  eq (← app (Sys.pidAlive pid : App Bool)) false "cgroup_kill_keeps: what ran in the scope is gone"
  eq (← durable t) d "cgroup_kill_keeps: the repo's durable state stays"

-- ---------- now_mono ----------

def now_mono (_ : T) : IO Unit := do
  let ok ← app (do
    let mut prev ← Clock.now
    for _ in [0:100000] do
      let x ← Clock.now
      if x < prev then return false
      prev := x
    return true : App Bool)
  eq ok true "now_mono: Clock.now never goes back"
  let t0 ← app (Clock.now : App Int)
  IO.sleep 1100
  eq (decide ((← app (Clock.now : App Int)) > t0)) true "now_mono: it moves on"

-- ---------- hc_ls_live, hc_run_starts, hc_send_targets, hc_kill_ends, hc_rm_keeps ----------

def hcOn : IO Bool := return (← IO.getEnv "SWARM_TEST_HC") == some "1"

/-- hc keeps its state under the real XDG_STATE_HOME (the fixture points it at a scratch dir; unset is this). -/
def hcSetup : IO Unit := do Shim.setenv "XDG_STATE_HOME" s!"{(← IO.getEnv "HOME").getD ""}/.local/state"

/-- Terminal `h` is listed live by `Agents.hcTerminals`. -/
def live (h : String) : IO Bool := do
  let some ts ← app (Agents.hcTerminals : App _) | fail "hc_ls_live: hc ls answers"
  return ts.any fun x => x.address == some h && x.state == some "live"

/-- This agent's own terminal, if any, is still live. -/
def hereLive : IO Bool := do
  match (← IO.getEnv "HC_TERMINAL_ID").filter (· ≠ "") with
  | some h => live h
  | none => pure true

/-- Starts `argv` in a terminal as `--restart` starts a watchd (Cmd/Watchd.lean's flags), killed and removed when the
test ends: its address and what hc printed. -/
def hcRun (t : T) (tag cwd : String) (argv : List String) : IO (String × Lean.Json) := do
  let r ← t.exec (["hc", "run", "--json", "--bg", "--no-parent", "--no-notify", "--name",
    s!"swarm-env-{← IO.Process.getPID}-{tag}", "--cwd", cwd, "--"] ++ argv)
  if r.code != 0 then fail s!"hc run: {r.stderr}"
  let j ← IO.ofExcept (Lean.Json.parse r.stdout)
  let some h := Json.fstr j "address" | fail s!"hc run printed no address: {r.stdout}"
  t.defer do discard <| t.exec ["hc", "kill", h]; discard <| t.exec ["hc", "rm", h]
  return (h, j)

/-- Waits up to 5 s for `p` to hold a line. -/
def waitLine (p : String) : IO Unit := do
  for _ in [0:50] do
    if ((← slurp p).getD "").contains '\n' then return
    IO.sleep 100

def hc_ls_live (t : T) : IO Unit := do
  if !(← hcOn) then return
  hcSetup
  let (h, _) ← hcRun t "ls" t.wt ["sleep", "300"]
  eq (← live h) true "hc_ls_live: a started terminal is listed live"
  discard <| t.exec ["hc", "kill", h]
  eq (← live h) false "hc_ls_live: a killed terminal is not"

def hc_run_starts (t : T) : IO Unit := do
  if !(← hcOn) then return
  hcSetup
  let pidf := t.d ++ "/hc-run.pid"
  let (h, j) ← hcRun t "run" t.wt ["sh", "-c", "echo $$ > \"$0\"; exec sleep 300", pidf]
  waitLine pidf
  let some pid := ((← slurp pidf).getD "").trimAscii.toString.toInt? | fail "hc_run_starts: the program it was given ran"
  eq (← app (Sys.pidAlive pid : App Bool)) true "hc_run_starts: the program it was given runs"
  if let some p := (j.getObjValAs? Int "pid").toOption then
    eq (← app (Sys.pidAlive p : App Bool)) true "hc_run_starts: the pid it printed runs"
  eq (← live h) true "hc_run_starts: in the live terminal it printed"

def hc_send_targets (t : T) : IO Unit := do
  if !(← hcOn) then return
  hcSetup
  let (fa, fb) := (t.d ++ "/typed-a", t.d ++ "/typed-b")
  -- two terminals that write what is typed into them to a file
  let (ta, _) ← hcRun t "a" t.d ["sh", "-c", "exec cat > \"$0\"", fa]
  let (tb, _) ← hcRun t "b" t.d ["sh", "-c", "exec cat > \"$0\"", fb]
  let g ← durable t
  -- swarm nudge's call (Cmd/Msgs.lean)
  let r ← t.exec ["hc", "send", ta, Cmd.Msgs.NUDGE]
  if r.code != 0 then fail s!"hc send: {r.stderr}"
  waitLine fa
  eq ((← slurp fa).getD "") (Cmd.Msgs.NUDGE ++ "\n") "hc_send_targets: the line is typed into that terminal"
  eq ((← slurp fb).getD "") "" "hc_send_targets: and into no other"
  eq ((← live ta) && (← live tb) && (← hereLive)) true "hc_send_targets: no terminal ends"
  eq (← durable t) g "hc_send_targets: the repo's durable state stays"

def hc_kill_ends (t : T) : IO Unit := do
  if !(← hcOn) then return
  hcSetup
  let (ha, _) ← hcRun t "ka" t.wt ["sleep", "300"]
  let (hb, _) ← hcRun t "kb" t.wt ["sleep", "300"]
  let g ← durable t
  discard <| t.exec ["hc", "kill", ha]
  eq (← live ha) false "hc_kill_ends: a killed terminal is not listed live"
  eq ((← live hb) && (← hereLive)) true "hc_kill_ends: no other terminal ends"
  eq (← durable t) g "hc_kill_ends: the repo's durable state stays"

def hc_rm_keeps (t : T) : IO Unit := do
  if !(← hcOn) then return
  hcSetup
  let (ha, _) ← hcRun t "ra" t.wt ["sleep", "300"]
  let (hb, _) ← hcRun t "rb" t.wt ["sleep", "300"]
  discard <| t.exec ["hc", "kill", ha]
  let g ← durable t
  discard <| t.exec ["hc", "rm", ha]
  eq ((← live hb) && (← hereLive)) true "hc_rm_keeps: no other terminal ends"
  eq (← durable t) g "hc_rm_keeps: the repo's durable state stays"

-- ---------- gh_checks, gh_state ----------
-- What Ci.ghList reads from `gh pr list` against what GitHub's REST API says of the same PRs: their check runs and
-- commit statuses, and whether they are merged (the merge commit then on the base, by git).

def ghOn : IO Bool := return (← IO.getEnv "SWARM_TEST_GH") == some "1"

/-- This repo's top level. -/
def top : IO String := do
  let r ← execIO' ["git", "rev-parse", "--show-toplevel"] { cwd := some (← swarmDir) }
  return strip r.stdout

def api (top path jq : String) : IO Lean.Json := do
  let r ← execIO' ["gh", "api", path, "--jq", jq] { cwd := some top }
  if r.code != 0 then fail s!"gh api {path}: {r.stderr}"
  IO.ofExcept (Lean.Json.parse r.stdout)

/-- The open and merged PRs among the latest six, as Ci.ghList reads them. -/
def prs (top : String) : IO (List Lean.Json) := do
  let o ← outputIO ["gh", "pr", "list", "--state", "all", "--limit", "6", "--json",
    "number,headRefOid,baseRefName,state,mergeCommit,statusCheckRollup"] (some top) []
  let some l := Ci.ghList o "" | fail "gh pr list answers"
  let l := l.filter fun x => Json.fstr x "state" == some "OPEN" || Json.fstr x "state" == some "MERGED"
  if l.isEmpty then fail "the repo has an open or merged PR"
  return l

def arr : Lean.Json → List Lean.Json
  | .arr a => a.toList
  | _ => []

def gh_checks (_ : T) : IO Unit := do
  if !(← ghOn) then return
  let top ← top
  for pr in ← prs top do
    let n := (pr.getObjValAs? Int "number").toOption.getD 0
    let sha := (Json.fstr pr "headRefOid").getD ""
    let runs := arr (← api top ("repos/{owner}/{repo}/commits/" ++ sha ++ "/check-runs?per_page=100")
      "[.check_runs[] | {status, conclusion}]")
    let sts := arr (← api top ("repos/{owner}/{repo}/commits/" ++ sha ++ "/status") "[.statuses[] | .state]")
    let mut want := if runs.length + sts.length > 0 then "green" else "pending"
    let mut red := false
    for r in runs do
      if Json.fstr r "status" != some "completed" then want := "pending"
      else if !["success", "neutral", "skipped"].contains ((Json.fstr r "conclusion").getD "") then red := true
    for st in sts do
      if st == .str "pending" then want := "pending" else if st != .str "success" then red := true
    if want == "green" && red then want := "red"
    let got := Ci.verdict (pr.getObjVal? "statusCheckRollup").toOption
    eq got want s!"gh_checks: PR #{n}: the rollup reads {got}, its check runs and statuses {want}"

def gh_state (_ : T) : IO Unit := do
  if !(← ghOn) then return
  let top ← top
  for pr in ← prs top do
    let n := (pr.getObjValAs? Int "number").toOption.getD 0
    let state := (Json.fstr pr "state").getD ""
    let merged := (← api top ("repos/{owner}/{repo}/pulls/" ++ toString n) ".merged") == .bool true
    eq (state == "MERGED") merged s!"gh_state: PR #{n} is {state}, and merged is {merged}"
    if merged then
      let base := (Json.fstr pr "baseRefName").getD ""
      let oid := ((pr.getObjVal? "mergeCommit").toOption.bind (Json.fstr · "oid")).getD ""
      discard <| execIO' ["git", "fetch", "-q", "origin", base] { cwd := some top }
      eq (← execIO' ["git", "merge-base", "--is-ancestor", oid, "origin/" ++ base] { cwd := some top }).code.toNat 0
        s!"gh_state: PR #{n}'s merge commit is on {base}"

def tests : List Case := [
  ("ancestor_reach", ancestor_reach),
  ("same_content_reach", same_content_reach),
  ("status_clean", status_clean),
  ("listed_on", listed_on),
  ("wt_remove", wt_remove),
  ("del_ref", del_ref),
  ("touched_recent", touched_recent),
  ("kill0_alive", kill0_alive),
  ("cwds_proc", cwds_proc),
  ("now_mono", now_mono),
  ("hc_ls_live", hc_ls_live),
  ("hc_run_starts", hc_run_starts),
  ("hc_send_targets", hc_send_targets),
  ("hc_kill_ends", hc_kill_ends),
  ("hc_rm_keeps", hc_rm_keeps),
  ("cgroup_kill_keeps", cgroup_kill_keeps),
  ("gh_checks", gh_checks),
  ("gh_state", gh_state)]

end SwarmLean.Tests.Spec.Env
