import SwarmLean.Store
import SwarmLean.Lib.Ci
import SwarmLean.Lib.Watchd

/-! Every assumption the proofs of swarm-lean make about the world outside the code, in one file (board #109).

The code reaches the world only through the classes of World.lean and Sys.lean; the proofs are about the functions it
runs, and nothing here is an axiom. Each assumption is a definition, a `Prop`, that a theorem takes as a hypothesis, so
a theorem reads "these assumptions about the world → this guarantee", and `Audit.lean` counts the theorems that take
each. They are swarm/model's `Env.lean` hypotheses moved onto the code's own calls, deduplicated with what #103-#106
used:

- the store: `Atomic`, the one assumption #103-#106 took, which also stands for Env.lean's five sqlite hypotheses
  (`SqliteBegin`, `SqliteRead`, `SqliteWrite`, `SqliteCommit`, `SqliteRollback`): the code runs every write as one
  `BEGIN IMMEDIATE … COMMIT` (`Store.txn`), and what those five give such a transaction is that concurrent ones apply
  in some order;
- the tools, through `Tools`: what a command line answers (`Proc.output`, `Git.git`), what `Sys.pidAlive`,
  `Sys.mtime`, `Clock.now` and `Machine.cwds` return, and what is true of the repo, the terminals, the processes and
  the PRs. Each assumption below says that one answer means one truth, as Env.lean's did of its `Tools`.

Each assumption names, in its `(env_spec: …)` or `(sqlite_spec: …)` tag, the case of swarm-tests (Tests/Spec/Env.lean,
Tests/Spec/Sqlite.lean) that tests it against the real tool (check.sh fails on a tag with no case there).
`consistent`: one machine has them all. -/

namespace SwarmLean
open Lean (Json)

/-- What "the store is well behaved" means, assumed of the real store and not proved: when processes ran their
requests `ran` (each with the answer it got) at once on a store holding `before` and left `after`, the requests
applied one after another in some order give those answers and `after` (sqlite_spec: sqlite_begin, sqlite_write,
sqlite_commit, sqlite_rollback). -/
def Atomic (step : τ → Db → Db × α) (before after : Db) (ran : List (τ × α)) : Prop :=
  ∃ order : List (τ × α), order.Perm ran ∧ replay step before (order.map (·.1)) = (after, order)

/-- The machine at one moment, as the assumptions read it: what the code's calls to the world answer there, the world
after a command, and what is true of the repo, hc's terminals, the processes and GitHub's PRs. Any value of this type
is a machine: each call may answer anything (a failed call is one of the answers). -/
structure Tools where
  /-- the machine at one moment -/
  World : Type
  /-- what `Proc.output argv cwd []` returns in `w`: exit code and output, none when the program could not run -/
  out : World → List String → Option String → Option ProcOut
  /-- what `Git.git args cwd` returns in `w`: git's stdout when it exits 0 -/
  git : World → List String → Option String → Option String
  /-- the machine after `argv` ran from `cwd` in `w` -/
  after : World → List String → Option String → World
  /-- what `Sys.pidAlive p` (kill(p, 0) == 0) returns in `w` -/
  pidAlive : World → Int → Bool
  /-- what `Sys.mtime path` returns in `w` -/
  mtime : World → String → Option Int
  /-- what `Clock.now` returns in `w` -/
  now : World → Int
  /-- the working directories `Machine.cwds` lists in `w`, none when it can't tell -/
  cwds : World → Option (List String)
  /-- `w'` comes after `w`, whatever the swarm and the world did in between -/
  Later : World → World → Prop
  /-- the repo, checked out at `cwd`, holds every change of commit `ref` in `b` (by ancestry or the same content) -/
  Holds : World → String → String → String → Prop
  /-- worktree `wt` is there -/
  There : World → String → Prop
  /-- worktree `wt` has something uncommitted, an untracked file included -/
  Dirty : World → String → Prop
  /-- branch `b`'s tip -/
  tip : World → String → Option String
  /-- some process's working directory is inside worktree `wt` -/
  Inside : World → String → Prop
  /-- worktree `wt` was used (an edit, a commit, a checkout) in the last `Watchd.SWEEP_IDLE` seconds -/
  Recent : World → String → Prop
  /-- hc's terminal `h` is live -/
  Live : World → String → Prop
  /-- process `p` is in the process table (running, or a zombie its parent has not reaped) -/
  Running : World → Int → Prop
  /-- the lines typed into terminal `h` so far, in order -/
  typed : World → String → List String
  /-- PR `p`'s head checks as GitHub runs them: "pending" until every check finished, then "green" or "red" -/
  checks : World → Int → String
  /-- PR `p` is merged into its base -/
  merged : World → Int → Bool

variable (M : Tools)

/-- The repo is the same in `w` and `w'`: every worktree there or not and dirty or not as it was, every branch tip,
and what each commit's changes are in. -/
def Tools.SameRepo (w w' : M.World) : Prop :=
  (∀ b, M.tip w' b = M.tip w b) ∧ (∀ x, (M.There w' x ↔ M.There w x) ∧ (M.Dirty w' x ↔ M.Dirty w x)) ∧
    ∀ cwd a b, M.Holds w' cwd a b ↔ M.Holds w cwd a b

/-- The command exited 0. -/
def Ok0 (o : Option ProcOut) : Prop := ∃ x, o = some x ∧ x.code = 0

/-! ### git -/

/-- git: `git -C cwd merge-base --is-ancestor ref b` exiting 0 means `b` holds `ref`'s changes (env_spec: ancestor_reach). -/
def AncestorReach : Prop := ∀ w cwd ref b,
  Ok0 (M.out w ["git", "-C", cwd, "merge-base", "--is-ancestor", ref, b] none) → M.Holds w cwd ref b

/-- git: when `git diff --name-only -z mb ref` lists some files, `mb` the merge base git printed, and
`git diff --quiet ref b -- <them>` exits 0, `b` holds `ref`'s changes: a squash or rebase merge
(Lifecycle.landedRef1's second check) (env_spec: same_content_reach). -/
def SameContentReach : Prop := ∀ w cwd ref b mb files o,
  M.out w ["git", "-C", cwd, "merge-base", b, ref] none = some o → o.code = 0 → strip o.stdout = mb →
  (∃ d, M.out w ["git", "-C", cwd, "diff", "--name-only", "-z", mb, ref] none = some d ∧ d.code = 0 ∧
    (d.stdout.splitOn "\x00").filter (· ≠ "") = files) → files ≠ [] →
  Ok0 (M.out w (["git", "-C", cwd, "diff", "--quiet", ref, b, "--"] ++ files) none) → M.Holds w cwd ref b

/-- git: a worktree that is there and whose `git -C wt status --porcelain` prints nothing but space has nothing
uncommitted, untracked files included (env_spec: status_clean). -/
def StatusClean : Prop := ∀ w wt o, M.There w wt →
  M.out w ["git", "-C", wt, "status", "--porcelain"] none = some o → o.code = 0 → strip o.stdout = "" → ¬ M.Dirty w wt

/-- git: a worktree `git worktree list --porcelain` lists is there (env_spec: listed_on). -/
def ListedOn : Prop := ∀ w cwd o p,
  M.out w ["git", "worktree", "list", "--porcelain"] cwd = some o → o.code = 0 → ("worktree " ++ p) ∈ splitlines o.stdout →
  M.There w p

/-- git: `git -C main worktree remove wt` takes a clean worktree away and nothing else (every branch, every other
worktree, every commit stay), and refuses a dirty one, changing nothing (env_spec: wt_remove). -/
def WtRemove : Prop := ∀ w main wt,
  let w' := M.after w ["git", "-C", main, "worktree", "remove", wt] none
  (M.There w wt ∧ ¬ M.Dirty w wt → ¬ M.There w' wt) ∧ (M.Dirty w wt → M.SameRepo w w') ∧
    (∀ b, M.tip w' b = M.tip w b) ∧ (∀ x, x ≠ wt → (M.There w' x ↔ M.There w x) ∧ (M.Dirty w' x ↔ M.Dirty w x)) ∧
    ∀ cwd a b, M.Holds w' cwd a b ↔ M.Holds w cwd a b

/-- git: `git -C main update-ref -d refs/heads/b k` deletes branch `b` if its tip is `k`, and else changes nothing; no
other branch, no worktree and no commit changes (env_spec: del_ref). -/
def DelRef : Prop := ∀ w main b k,
  let w' := M.after w ["git", "-C", main, "update-ref", "-d", "refs/heads/" ++ b, k] none
  M.tip w' b = (if M.tip w b = some k then none else M.tip w b) ∧ (∀ b', b' ≠ b → M.tip w' b' = M.tip w b') ∧
    (∀ x, (M.There w' x ↔ M.There w x) ∧ (M.Dirty w' x ↔ M.Dirty w x)) ∧ ∀ cwd a c, M.Holds w' cwd a c ↔ M.Holds w cwd a c

/-! ### hc -/

/-- The terminals `hc ls --json` prints, as `Agents.hcTerminals` reads them: (address, state) of each. -/
def lsTerms (o : ProcOut) : Option (List (Option String × Option String)) :=
  let str (x : Json) (k : String) : Option String := (x.getObjValAs? String k).toOption
  match (Json.parse o.stdout).toOption with
  | none => none
  | some j => match j.getObjVal? "terminals" with
    | .ok (.arr ts) => some (ts.toList.map fun x => (str x "address", str x "state"))
    | .ok (.obj _) => some []
    | _ => none

/-- hc: when `hc ls --json` answers, it lists a terminal as live exactly when it is (when it does not answer the
code reads no list and reaps nothing) (env_spec: hc_ls_live). -/
def HcLsLive : Prop := ∀ w o ts h, M.out w ["hc", "ls", "--json"] none = some o → o.code = 0 → lsTerms o = some ts →
  ((some h, some "live") ∈ ts ↔ M.Live w h)

/-- hc: `hc kill h` ends terminal `h` and leaves the repo as it was (env_spec: hc_kill_ends). -/
def HcKillEnds : Prop := ∀ w h, ¬ M.Live (M.after w ["hc", "kill", h] none) h ∧ M.SameRepo w (M.after w ["hc", "kill", h] none)

/-- hc: `hc send h l` to a live terminal types `l` into `h` and into no other terminal, starts or ends no terminal and
leaves the repo as it was (`swarm nudge`) (env_spec: hc_send_targets). -/
def HcSendTargets : Prop := ∀ w h l, M.Live w h →
  let w' := M.after w ["hc", "send", h, l] none
  M.typed w' h = M.typed w h ++ [l] ∧ (∀ h', h' ≠ h → M.typed w' h' = M.typed w h') ∧ (∀ h', M.Live w' h' ↔ M.Live w h') ∧
    M.SameRepo w w'

/-- hc: `hc run --json --bg …` that exits 0 started the program: the terminal whose address it prints is live and the
pid it prints runs (watchd's `--restart`) (env_spec: hc_run_starts). -/
def HcRunStarts : Prop := ∀ w rest o, M.out w (["hc", "run", "--json", "--bg"] ++ rest) none = some o → o.code = 0 →
  ∀ j, Json.parse o.stdout = .ok j →
  (∀ h, Json.fstr j "address" = some h → M.Live (M.after w (["hc", "run", "--json", "--bg"] ++ rest) none) h) ∧
  (∀ p, (j.getObjValAs? Int "pid").toOption = some p → M.Running (M.after w (["hc", "run", "--json", "--bg"] ++ rest) none) p)

/-! ### processes, files, the clock -/

/-- processes: `kill(p, 0)` is 0 exactly when process `p` is in the process table, a zombie included (env_spec: kill0_alive). -/
def Kill0Alive : Prop := ∀ w p, M.pidAlive w p = true ↔ M.Running w p

/-- processes: `Machine.cwds`, when it answers, lists a directory inside every worktree a process sits in (Linux: each
/proc/<pid>/cwd; macOS: lsof) (env_spec: cwds_proc). -/
def CwdsProc : Prop := ∀ w wt cs, M.cwds w = some cs → M.Inside w wt → ∃ c ∈ cs, Watchd.inside c wt = true

/-- filesystem: a worktree used in the last `SWEEP_IDLE` seconds reads as touched then: the later mtime of its directory
and of its git dir's `logs/HEAD` (`gd`, what `git rev-parse --absolute-git-dir` printed) is within that (env_spec:
touched_recent). -/
def TouchedRecent : Prop := ∀ w wt gd, M.Recent w wt → M.git w ["-C", wt, "rev-parse", "--absolute-git-dir"] none = some gd →
  M.now w - max ((M.mtime w wt).getD 0) ((M.mtime w (joinPath (joinPath (strip gd) "logs") "HEAD")).getD 0) < Watchd.SWEEP_IDLE

/-- clock: `Clock.now` never goes back (a clock stepped back would read a lapsed lease live again) (env_spec: now_mono). -/
def NowMono : Prop := ∀ w w', M.Later w w' → M.now w ≤ M.now w'

/-! ### gh -/

/-- The PR list `gh pr list --state all --limit 50 --json …` prints (ci.pr_watch's poll), as `Ci.ghList` reads it. -/
def prList (o : ProcOut) : Option (List Json) := Ci.ghList (some o) ""

/-- gh: the verdict `Ci.verdict` reads off a listed PR's `statusCheckRollup` is the state of its head's checks
(env_spec: gh_checks). -/
def GhChecks : Prop := ∀ w repo fields o prs x p,
  M.out w ["gh", "pr", "list", "--state", "all", "--limit", "50", "--json", fields] repo = some o → prList o = some prs →
  x ∈ prs → (x.getObjValAs? Int "number").toOption = some p →
  Ci.verdict (x.getObjVal? "statusCheckRollup").toOption = M.checks w p

/-- gh: a listed PR that is not closed has state MERGED when it is merged, else OPEN (env_spec: gh_state). -/
def GhState : Prop := ∀ w repo fields o prs x p,
  M.out w ["gh", "pr", "list", "--state", "all", "--limit", "50", "--json", fields] repo = some o → prList o = some prs →
  x ∈ prs → (x.getObjValAs? Int "number").toOption = some p → Json.fstr x "state" ≠ some "CLOSED" →
  Json.fstr x "state" = some (if M.merged w p then "MERGED" else "OPEN")

/-- A machine on which no command runs and nothing is live, used, merged or later than anything. -/
def Tools.idle : Tools where
  World := Unit
  out _ _ _ := none
  git _ _ _ := none
  after w _ _ := w
  pidAlive _ _ := false
  mtime _ _ := none
  now _ := 0
  cwds _ := none
  Later _ _ := True
  Holds _ _ _ _ := False
  There _ _ := False
  Dirty _ _ := False
  tip _ _ := none
  Inside _ _ := False
  Recent _ _ := False
  Live _ _ := False
  Running _ _ := False
  typed _ _ := []
  checks _ _ := "pending"
  merged _ _ := false

/-- The tool assumptions hold together: the idle machine has them all. That the real tools have them is what
swarm-tests' env_spec cases test. -/
theorem consistent : AncestorReach .idle ∧ SameContentReach .idle ∧ StatusClean .idle ∧ ListedOn .idle ∧
    WtRemove .idle ∧ DelRef .idle ∧ HcLsLive .idle ∧ HcKillEnds .idle ∧ HcSendTargets .idle ∧ HcRunStarts .idle ∧
    Kill0Alive .idle ∧ CwdsProc .idle ∧ TouchedRecent .idle ∧ NowMono .idle ∧ GhChecks .idle ∧ GhState .idle := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [AncestorReach, SameContentReach, StatusClean, ListedOn, WtRemove, DelRef, HcLsLive, HcKillEnds, HcSendTargets,
      HcRunStarts, Kill0Alive, CwdsProc, TouchedRecent, NowMono, GhChecks, GhState, Tools.idle, Tools.SameRepo, Ok0]

end SwarmLean
