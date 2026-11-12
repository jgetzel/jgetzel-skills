import SwarmModel.Model
import SwarmModel.Iso
import SwarmModel.PrWatch

/-! The environment (board #34, #68): what the model may assume about the world outside the swarm's db, and about
sqlite itself (board #33, at the end), in one file. `Tools` is what the swarm runs (git, hc, gh, the kernel's process table, the filesystem, the clock) and `Tools.git`
is the model's view of the repo: commits as patch sets, branches, worktree slots, under the replay's name map (a slot
is a worktree path, a branch id a branch name, a commit id a sha).

The rule (board #68): unproved code (hc, git, gh, sqlite, the OS) is untrusted. A `Tools` or a `Db` is any machine: each
tool call may return any value of its type (a failed call is one of them: `hc ls` that does not answer is the model's
`hcSees` off). Trust enters only as the named hypotheses below, small independent `Prop`s on a `Tools` or `Db`, each
taken by a theorem as a hypothesis, in the direction its proof uses; there is no axiom and no bundle of them. A
theorem is "these assumptions about the outside world → this guarantee". `Trust.lean` shows each hypothesis a theorem
takes is needed: a machine with every other one where the guarantee fails. Each is tested against the real tool by the
case named in its `(env_spec: …)` or `(sqlite_spec: …)` tag, in `../lua/test/`; check.sh fails on a tag with no case,
Audit.lean on a hypothesis with no tag. `consistent` and `sqlite_consistent`: an ideal machine has them all, so
together they are satisfiable. -/

namespace Swarm.Env

/-- what the swarm runs, and what it acts on -/
structure Tools where
  /-- the machine at one moment: the repo, hc's terminals, processes, files, the clock -/
  World : Type
  /-- the model's view of the repo at that moment -/
  git : World → Git
  /-- `git merge-base --is-ancestor <k> <b>` exits 0 (commit k, branch b) -/
  isAncestor : World → Nat → Nat → Bool
  /-- landed_ref's content check: `git diff --name-only -z $(git merge-base b k) k` lists some files, and
  `git diff --quiet k b -- <them>` exits 0 -/
  sameContent : World → Nat → Nat → Bool
  /-- `git -C <worktree x> status --porcelain` prints nothing -/
  statusClean : World → Nat → Bool
  /-- `git worktree list --porcelain` lists worktree x -/
  listed : World → Nat → Bool
  /-- `git worktree remove <worktree x>` -/
  wtRemove : World → Nat → World
  /-- `git update-ref -d refs/heads/<b> <k>` -/
  delRef : World → Nat → Nat → World
  /-- terminal h is live -/
  termLive : World → Nat → Bool
  /-- `hc ls --json` lists terminal h with state "live" -/
  hcLs : World → Nat → Bool
  /-- `hc kill h` -/
  hcKill : World → Nat → World
  /-- `hc send h <line>`: the line pasted into terminal h and submitted with Enter (`swarm nudge`) -/
  hcSend : World → Nat → String → World
  /-- the lines typed into terminal h so far, in order -/
  typed : World → Nat → List String
  /-- `hc run --json --bg --no-parent --no-notify -- <cmd>` (watchd's `--restart`) -/
  hcRun : World → World
  /-- the address `hc run` prints -/
  hcRunAddr : World → Nat
  /-- the pid of the program it started -/
  hcRunPid : World → Nat
  /-- process p is in the process table: running, or dead and not yet reaped by its parent (a zombie) -/
  alive : World → Nat → Bool
  /-- `kill(p, 0)` returns 0 (posix.signal) -/
  kill0 : World → Nat → Bool
  /-- `machine.cwds()` has a process whose cwd is inside worktree x (watchd.inside) -/
  cwdIn : World → Nat → Bool
  /-- `os.time()` (util.now) -/
  now : World → Nat
  /-- what the sweep reads as worktree x's last touch: the later mtime of its directory and its `logs/HEAD` -/
  touched : World → Nat → Nat
  /-- w' comes after w: whatever the swarm and the world did in between -/
  Later : World → World → Prop
  /-- PR p's head's checks as GitHub runs them (board #28) -/
  prChecks : World → Nat → Checks
  /-- PR p is merged into its base -/
  prMerged : World → Nat → Bool
  /-- ci.verdict of PR p's `statusCheckRollup` in `gh pr list --json` -/
  ghVerdict : World → Nat → String
  /-- PR p's `state` in `gh pr list --json`, for a PR the poll keeps (ci.pr_watch drops closed ones) -/
  ghState : World → Nat → String

/-- watchd.SWEEP_IDLE: a worktree untouched this long (s) may be swept -/
def sweepIdle : Nat := 1800

/-- what a worktree keeps that time and processes don't change: there or not, its branch, HEAD, dirty or not; every
branch tip; every commit -/
def Git.durable (g : Git) : List (Bool × Option Nat × Nat × Bool) × List (Option Nat) × List Commit :=
  (g.wts.map fun x => (x.on, x.br, x.head, x.dirty), g.brs, g.cm)

variable (t : Tools)

/-- git: k an ancestor of b's tip means b holds k's patches (a commit is its parent's tree plus its own change; the
model's commits only add files) (env_spec: ancestor_reach) -/
def AncestorReach : Prop := ∀ w k b, t.isAncestor w k b = true → (t.git w).reachFrom k b = true
/-- git: b's tip has, byte for byte, every file k changed since their merge base, so b holds k's patches (a squash or
rebase merge) (env_spec: same_content_reach) -/
def SameContentReach : Prop := ∀ w k b, t.sameContent w k b = true → (t.git w).reachFrom k b = true
/-- git: a worktree that is there and has an empty `status --porcelain` has nothing uncommitted (untracked files
included); the sweep needs no more (the case tests both directions) (env_spec: status_clean) -/
def StatusClean : Prop := ∀ w x, ((t.git w).wt x).on = true → t.statusClean w x = true → ((t.git w).wt x).dirty = false
/-- git: a worktree `worktree list` lists is there (env_spec: listed_on) -/
def ListedOn : Prop := ∀ w x, t.listed w x = true → ((t.git w).wt x).on = true
/-- git: `worktree remove` takes a clean worktree away and nothing else (its branch, every other worktree and every
commit stay), and refuses a dirty one, changing nothing (env_spec: wt_remove) -/
def WtRemove : Prop := ∀ w x, t.git (t.wtRemove w x) =
  if ((t.git w).wt x).on && !((t.git w).wt x).dirty then (t.git w).setWt x ({ · with on := false }) else t.git w
/-- git: `update-ref -d refs/heads/b k` deletes branch b if its tip is k, and else changes nothing (env_spec: del_ref) -/
def DelRef : Prop := ∀ w b k, t.git (t.delRef w b k) =
  if (t.git w).tip b = some k then { t.git w with brs := (t.git w).brs.set b none } else t.git w
/-- hc: `hc ls` lists a terminal as live exactly when it is (when it answers at all: else the model's `hcSees` is off)
(env_spec: hc_ls_live) -/
def HcLsLive : Prop := ∀ w h, t.hcLs w h = t.termLive w h
/-- hc: `hc ls` lists a live terminal as live: `HcLsLive`'s one direction (env_spec: hc_ls_live) -/
def HcLsShows : Prop := ∀ w h, t.termLive w h = true → t.hcLs w h = true
/-- hc: `hc kill h` ends terminal h and leaves the repo's durable state alone (the processes it ends may leave
worktrees, so `proc` may change). That it ends no other terminal no theorem needs (the case tests it too)
(env_spec: hc_kill_ends) -/
def HcKillEnds : Prop := ∀ w h, t.termLive (t.hcKill w h) h = false ∧ Git.durable (t.git (t.hcKill w h)) = Git.durable (t.git w)
/-- hc: `hc send h l` to a live terminal types l into h and into no other terminal, starts or ends no terminal, and
leaves the repo's durable state alone (what the program in h then does with the line is its own turn) (env_spec: hc_send_targets) -/
def HcSendTargets : Prop := ∀ w h l, t.termLive w h = true →
  t.typed (t.hcSend w h l) h = t.typed w h ++ [l] ∧ (∀ h', h' ≠ h → t.typed (t.hcSend w h l) h' = t.typed w h') ∧
  (∀ h', t.termLive (t.hcSend w h l) h' = t.termLive w h') ∧ Git.durable (t.git (t.hcSend w h l)) = Git.durable (t.git w)
/-- hc: `hc run --bg` starts the program: the terminal whose address it prints is live, and the program runs in it, a
process (the model's `restart`: the new watchd runs, in its hidden terminal) (env_spec: hc_run_starts) -/
def HcRunStarts : Prop := ∀ w, t.termLive (t.hcRun w) (t.hcRunAddr w) = true ∧ t.alive (t.hcRun w) (t.hcRunPid w) = true
/-- processes: `kill(p, 0)` is 0 exactly when process p is in the process table, a zombie included (that p is still
*our* process, no pid reuse, is the model's reading, not this) (env_spec: kill0_alive) -/
def Kill0Alive : Prop := ∀ w p, t.kill0 w p = t.alive w p
/-- processes: `kill(p, 0)` finds a process in the table: `Kill0Alive`'s one direction (env_spec: kill0_alive) -/
def Kill0Finds : Prop := ∀ w p, t.alive w p = true → t.kill0 w p = true
/-- processes: `machine.cwds()` sees a cwd inside worktree x whenever the model's `proc` flag is set (Linux: every
/proc/<pid>/cwd; macOS: lsof, own processes); the case tests both directions (env_spec: cwds_proc) -/
def CwdsProc : Prop := ∀ w x, ((t.git w).wt x).proc = true → t.cwdIn w x = true
/-- filesystem: the model's `recent` is the sweep's reading of mtimes: touched within `sweepIdle`. A commit or checkout
touches `logs/HEAD`; an edit of a file below the top directory touches neither, though the model's `edit` sets
`recent`: that edit leaves the worktree dirty, and the sweep never takes a dirty one, so nothing it decides differs.
Only that a `recent` worktree reads as touched is needed (the case tests both directions) (env_spec: touched_recent) -/
def TouchedRecent : Prop := ∀ w x, ((t.git w).wt x).recent = true → t.now w < t.touched w x + sweepIdle
/-- clock: `os.time()` never goes back (NTP stepping the clock back breaks it: a lapsed lease would read live again) (env_spec: now_mono) -/
def NowMono : Prop := ∀ w w', t.Later w w' → t.now w ≤ t.now w'
/-- `gh pr list`'s statusCheckRollup, read by ci.verdict, is the state of the head's checks: pending until every check
has finished, then green or red (env_spec: gh_checks) -/
def GhChecks : Prop := ∀ w p, t.ghVerdict w p = (t.prChecks w p).name
/-- `gh pr list`'s state of a PR the poll keeps is MERGED when it is merged, else OPEN (env_spec: gh_state) -/
def GhState : Prop := ∀ w p, t.ghState w p = if t.prMerged w p then "MERGED" else "OPEN"

/-- a machine where every tool tells the truth: the repo, the live terminals, the live processes, and the clock
(offset by `sweepIdle`, so an untouched worktree has a last touch) -/
structure IdealWorld where
  git : Git
  terms : Nat → Bool
  inputs : Nat → List String
  procs : Nat → Bool
  clock : Nat
  checks : Nat → Checks
  merged : Nat → Bool

def ideal : Tools where
  World := IdealWorld
  git := IdealWorld.git
  isAncestor w k b := w.git.reachFrom k b
  sameContent w k b := w.git.reachFrom k b
  statusClean w x := !(w.git.wt x).dirty
  listed w x := (w.git.wt x).on
  wtRemove w x := if (w.git.wt x).on && !(w.git.wt x).dirty then { w with git := w.git.setWt x ({ · with on := false }) } else w
  delRef w b k := if w.git.tip b = some k then { w with git := { w.git with brs := w.git.brs.set b none } } else w
  termLive w h := w.terms h
  hcLs w h := w.terms h
  hcKill w h := { w with terms := fun h' => h' != h && w.terms h' }
  hcSend w h l := { w with inputs := fun h' => if h' = h then w.inputs h' ++ [l] else w.inputs h' }
  typed w h := w.inputs h
  hcRun w := { w with terms := fun h => h == 0 || w.terms h, procs := fun p => p == 0 || w.procs p }
  hcRunAddr _ := 0
  hcRunPid _ := 0
  alive w p := w.procs p
  kill0 w p := w.procs p
  cwdIn w x := (w.git.wt x).proc
  now w := w.clock + sweepIdle
  touched w x := if (w.git.wt x).recent then w.clock + sweepIdle else w.clock
  Later w w' := w.clock ≤ w'.clock
  prChecks w p := w.checks p
  prMerged w p := w.merged p
  ghVerdict w p := (w.checks p).name
  ghState w p := if w.merged p then "MERGED" else "OPEN"

/-- the assumptions hold together: the ideal machine has them all -/
theorem consistent : AncestorReach ideal ∧ SameContentReach ideal ∧ StatusClean ideal ∧ ListedOn ideal ∧ WtRemove ideal ∧
    DelRef ideal ∧ HcLsLive ideal ∧ HcLsShows ideal ∧ HcKillEnds ideal ∧ HcSendTargets ideal ∧ HcRunStarts ideal ∧
    Kill0Alive ideal ∧ Kill0Finds ideal ∧ CwdsProc ideal ∧ TouchedRecent ideal ∧ NowMono ideal ∧ GhChecks ideal ∧
    GhState ideal :=
  ⟨fun _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => by simpa [ideal] using h, fun _ _ h => h,
   fun _ _ => apply_ite IdealWorld.git _ _ _, fun _ _ _ => apply_ite IdealWorld.git _ _ _, fun _ _ => rfl,
   fun _ _ h => h, fun _ _ => ⟨by simp [ideal], rfl⟩,
   fun _ _ _ _ => ⟨by simp [ideal], fun _ hh => by simp [ideal, hh], fun _ => rfl, rfl⟩,
   fun _ => ⟨by simp [ideal], by simp [ideal]⟩, fun _ _ => rfl, fun _ _ h => h, fun _ _ h => h,
   fun w x h => by simp_all [ideal, sweepIdle], fun _ _ h => Nat.add_le_add_right h _, fun _ _ => rfl, fun _ _ => rfl⟩

/-! ## sqlite (board #33)

The db as the swarm's processes see it: `Iso.lean`'s engine (committed versions, the write lock, each connection's
transaction, SQLITE_BUSY), on `Sql.lean`'s statements (`Iso.sqlLang`), with the code's choices (`Iso.Cfg`'s defaults:
`begin immediate`; WAL and `busy_timeout(10000)` on every connection, as db.lua sets them). One assumption per kind of
operation: it does what the engine says. They are sqlite's documented guarantees for a WAL db (isolation.html,
wal.html, lang_transaction.html), not a model of its internals; each is stress-tested against real sqlite through
db.lua, many processes at once, by the case its tag names in `../lua/test/sqlite_spec.lua`. -/

/-- sqlite as the swarm's processes see it -/
structure Db where
  World : Type
  /-- the engine's reading of the db: its committed versions, each connection's transaction, who holds the write lock,
  and (ghost) the statements each transaction ran -/
  view : World → Iso.Eng Sql.DB (Sql.Stmt × List Sql.Val)
  /-- connection c asked op, got r, and the world became w'. sqlite takes each op at one point (it orders access to
  the db file and the WAL index with locks, and a statement's rows all come from the snapshot its first step took), so
  a run is a sequence of these -/
  Does : World → Nat → Iso.Op (Sql.Stmt × List Sql.Val) → Iso.Res Sql.Out → World → Prop

/-- a run of the db: one op after another -/
inductive Db.Run (db : Db) (w0 : db.World) : db.World → Prop
  | refl : db.Run w0 w0
  | step {w w' c op r} : db.Run w0 w → db.Does w c op r w' → db.Run w0 w'

/-- the ops k picks do what the engine does with the code's `Cfg`, waiting out the busy timeout or not (t) -/
def Db.ByEngine (db : Db) (k : Iso.Op (Sql.Stmt × List Sql.Val) → Prop) : Prop :=
  ∀ w c op r w', k op → db.Does w c op r w' → ∃ t, Iso.step {} Iso.sqlLang (db.view w) c op t = some (r, db.view w')

variable (db : Db)

/-- `begin immediate`: takes the write lock if no connection holds it, and the transaction runs on the latest
committed version; else waits, and gets SQLITE_BUSY once busy_timeout runs out, nothing changed; inside a transaction
it is an error (sqlite_spec: sqlite_begin) -/
def SqliteBegin : Prop := db.ByEngine (· = .begin)
/-- a statement that only reads: runs on the latest committed version outside a transaction, on the transaction's own
db inside one; it never waits (WAL: readers don't block on the writer) (sqlite_spec: sqlite_read) -/
def SqliteRead : Prop := db.ByEngine fun op => ∃ s, op = .stmt s ∧ Iso.sqlLang.writes s = false
/-- a statement that writes: outside a transaction it waits for the write lock (SQLITE_BUSY once busy_timeout runs out,
nothing changed), runs on the latest committed version and commits at once, all or nothing; inside one it runs on the
transaction's db; an error changes nothing (sqlite_spec: sqlite_write) -/
def SqliteWrite : Prop := db.ByEngine fun op => ∃ s, op = .stmt s ∧ Iso.sqlLang.writes s = true
/-- `commit`: the transaction's db becomes the next committed version, all at once, and the lock is freed; WAL: it
never waits (sqlite_spec: sqlite_commit) -/
def SqliteCommit : Prop := db.ByEngine (· = .commit)
/-- `rollback`, and the process ending (exit or kill -9) in a transaction: the transaction's writes are discarded and
the lock is freed (sqlite_spec: sqlite_rollback) -/
def SqliteRollback : Prop := db.ByEngine fun op => op = .rollback ∨ op = .close

/-- a db that is the engine -/
def idealDb : Db where
  World := Iso.Eng Sql.DB (Sql.Stmt × List Sql.Val)
  view := id
  Does w c op r w' := ∃ t, Iso.step {} Iso.sqlLang w c op t = some (r, w')

/-- the assumptions hold together: the engine has them all -/
theorem sqlite_consistent : SqliteBegin idealDb ∧ SqliteRead idealDb ∧ SqliteWrite idealDb ∧ SqliteCommit idealDb ∧
    SqliteRollback idealDb :=
  ⟨fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ _ h => h, fun _ _ _ _ _ _ h => h,
   fun _ _ _ _ _ _ h => h⟩

end Swarm.Env
