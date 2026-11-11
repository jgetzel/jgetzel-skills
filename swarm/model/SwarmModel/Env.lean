import SwarmModel.Model
import SwarmModel.Iso

/-! The environment (board #34): every assumption the model makes about the world outside the swarm's db, and about
sqlite itself (board #33, at the end), in one file. `Tools` is what the swarm runs (git, hc, the kernel's process table, the filesystem, the clock) and `Tools.git`
is the model's view of the repo: commits as patch sets, branches, worktree slots, under the replay's name map (a slot
is a worktree path, a branch id a branch name, a commit id a sha). Each assumption is a `Prop` on `Tools` and an
axiom about `real`, the machine the swarm runs on; `check.sh` refuses a theorem resting on any axiom but these and
Lean's three. Each is tested against the real tool by the case of its own name in `../lua/test/env_spec.lua`.

Only the direction the code needs is assumed: a tool saying "landed" means landed, not the converse (W1, safety, needs
the first; nothing proved here needs the second). `consistent` shows the assumptions hold together of an ideal machine,
and `real` is defined as that machine, so they can't prove `False`. -/

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

/-- watchd.SWEEP_IDLE: a worktree untouched this long (s) may be swept -/
def sweepIdle : Nat := 1800

/-- what a worktree keeps that time and processes don't change: there or not, its branch, HEAD, dirty or not; every
branch tip; every commit -/
def Git.durable (g : Git) : List (Bool × Option Nat × Nat × Bool) × List (Option Nat) × List Commit :=
  (g.wts.map fun x => (x.on, x.br, x.head, x.dirty), g.brs, g.cm)

variable (t : Tools)

/-- git: k an ancestor of b's tip means b holds k's patches (a commit is its parent's tree plus its own change; the
model's commits only add files) -/
def AncestorReach : Prop := ∀ w k b, t.isAncestor w k b = true → (t.git w).reachFrom k b = true
/-- git: b's tip has, byte for byte, every file k changed since their merge base, so b holds k's patches (a squash or
rebase merge) -/
def SameContentReach : Prop := ∀ w k b, t.sameContent w k b = true → (t.git w).reachFrom k b = true
/-- git: a worktree that is there has an empty `status --porcelain` exactly when nothing in it is uncommitted
(untracked files included) -/
def StatusClean : Prop := ∀ w x, ((t.git w).wt x).on = true → (t.statusClean w x = !((t.git w).wt x).dirty)
/-- git: `worktree list` lists exactly the worktrees that are there -/
def ListedOn : Prop := ∀ w x, t.listed w x = ((t.git w).wt x).on
/-- git: `worktree remove` takes a clean worktree away and nothing else (its branch, every other worktree and every
commit stay), and refuses a dirty one, changing nothing -/
def WtRemove : Prop := ∀ w x, t.git (t.wtRemove w x) =
  if ((t.git w).wt x).on && !((t.git w).wt x).dirty then (t.git w).setWt x ({ · with on := false }) else t.git w
/-- git: `update-ref -d refs/heads/b k` deletes branch b if its tip is k, and else changes nothing -/
def DelRef : Prop := ∀ w b k, t.git (t.delRef w b k) =
  if (t.git w).tip b = some k then { t.git w with brs := (t.git w).brs.set b none } else t.git w
/-- hc: `hc ls` lists a terminal as live exactly when it is (when it answers at all: else the model's `hcSees` is off) -/
def HcLsLive : Prop := ∀ w h, t.hcLs w h = t.termLive w h
/-- hc: `hc kill h` ends terminal h, no other, and leaves the repo's durable state alone (the processes it ends may
leave worktrees, so `proc` may change) -/
def HcKillEnds : Prop := ∀ w h, t.termLive (t.hcKill w h) h = false ∧
  (∀ h', h' ≠ h → t.termLive (t.hcKill w h) h' = t.termLive w h') ∧ Git.durable (t.git (t.hcKill w h)) = Git.durable (t.git w)
/-- processes: `kill(p, 0)` is 0 exactly when process p is in the process table, a zombie included (that p is still
*our* process, no pid reuse, is the model's reading, not this) -/
def Kill0Alive : Prop := ∀ w p, t.kill0 w p = t.alive w p
/-- processes: `machine.cwds()` sees a cwd inside worktree x exactly when the model's `proc` flag is set (Linux: every
/proc/<pid>/cwd; macOS: lsof, own processes) -/
def CwdsProc : Prop := ∀ w x, t.cwdIn w x = ((t.git w).wt x).proc
/-- filesystem: the model's `recent` is the sweep's reading of mtimes: touched within `sweepIdle`. A commit or checkout
touches `logs/HEAD`; an edit of a file below the top directory touches neither, though the model's `edit` sets
`recent`: that edit leaves the worktree dirty, and the sweep never takes a dirty one, so nothing it decides differs -/
def TouchedRecent : Prop := ∀ w x, ((t.git w).wt x).recent = decide (t.now w < t.touched w x + sweepIdle)
/-- clock: `os.time()` never goes back (NTP stepping the clock back breaks it: a lapsed lease would read live again) -/
def NowMono : Prop := ∀ w w', t.Later w w' → t.now w ≤ t.now w'

/-- all of them -/
structure Sound : Prop where
  ancestorReach : AncestorReach t
  sameContentReach : SameContentReach t
  statusClean : StatusClean t
  listedOn : ListedOn t
  wtRemove : WtRemove t
  delRef : DelRef t
  hcLsLive : HcLsLive t
  hcKillEnds : HcKillEnds t
  kill0Alive : Kill0Alive t
  cwdsProc : CwdsProc t
  touchedRecent : TouchedRecent t
  nowMono : NowMono t

/-- a machine where every tool tells the truth: the repo, the live terminals, the live processes, and the clock
(offset by `sweepIdle`, so an untouched worktree has a last touch) -/
structure IdealWorld where
  git : Git
  terms : Nat → Bool
  procs : Nat → Bool
  clock : Nat

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
  alive w p := w.procs p
  kill0 w p := w.procs p
  cwdIn w x := (w.git.wt x).proc
  now w := w.clock + sweepIdle
  touched w x := if (w.git.wt x).recent then w.clock + sweepIdle else w.clock
  Later w w' := w.clock ≤ w'.clock

/-- the assumptions hold together: the ideal machine has them all -/
theorem consistent : Sound ideal where
  ancestorReach _ _ _ h := h
  sameContentReach _ _ _ h := h
  statusClean _ _ _ := rfl
  listedOn _ _ := rfl
  wtRemove w x := apply_ite IdealWorld.git _ _ _
  delRef w b k := apply_ite IdealWorld.git _ _ _
  hcLsLive _ _ := rfl
  hcKillEnds w h := ⟨by simp [ideal], fun h' hh => by simp [ideal, hh], rfl⟩
  kill0Alive _ _ := rfl
  cwdsProc _ _ := rfl
  touchedRecent w x := by simp only [ideal]; split <;> simp_all [sweepIdle]
  nowMono _ _ h := Nat.add_le_add_right h _

instance : Inhabited Tools := ⟨ideal⟩

/-- the machine the swarm runs on -/
opaque real : Tools

/-- `merge-base --is-ancestor` (env_spec: ancestor_reach) -/
axiom ancestor_reach : AncestorReach real
/-- landed_ref's squash check (env_spec: same_content_reach) -/
axiom same_content_reach : SameContentReach real
/-- `status --porcelain` (env_spec: status_clean) -/
axiom status_clean : StatusClean real
/-- `worktree list` (env_spec: listed_on) -/
axiom listed_on : ListedOn real
/-- `worktree remove` (env_spec: wt_remove) -/
axiom wt_remove : WtRemove real
/-- `update-ref -d` (env_spec: del_ref) -/
axiom del_ref : DelRef real
/-- `hc ls` (env_spec: hc_ls_live) -/
axiom hc_ls_live : HcLsLive real
/-- `hc kill` (env_spec: hc_kill_ends) -/
axiom hc_kill_ends : HcKillEnds real
/-- `kill(p, 0)` (env_spec: kill0_alive) -/
axiom kill0_alive : Kill0Alive real
/-- `machine.cwds()` (env_spec: cwds_proc) -/
axiom cwds_proc : CwdsProc real
/-- mtimes and SWEEP_IDLE (env_spec: touched_recent) -/
axiom touched_recent : TouchedRecent real
/-- `os.time()` (env_spec: now_mono) -/
axiom now_mono : NowMono real

/-! ## sqlite (board #33)

The db as the swarm's processes see it: `Iso.lean`'s engine (committed versions, the write lock, each connection's
transaction, SQLITE_BUSY), on `Sql.lean`'s statements (`Iso.sqlLang`), with the code's choices (`Iso.Cfg`'s defaults:
`begin immediate`; WAL and `busy_timeout(10000)` on every connection, as db.lua sets them). One assumption per kind of
operation: it does what the engine says. They are sqlite's documented guarantees for a WAL db (isolation.html,
wal.html, lang_transaction.html), not a model of its internals; each is stress-tested against real sqlite through
db.lua, many processes at once, by the case of its name in `../lua/test/sqlite_spec.lua`. -/

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
it is an error -/
def SqliteBegin : Prop := db.ByEngine (· = .begin)
/-- a statement that only reads: runs on the latest committed version outside a transaction, on the transaction's own
db inside one; it never waits (WAL: readers don't block on the writer) -/
def SqliteRead : Prop := db.ByEngine fun op => ∃ s, op = .stmt s ∧ Iso.sqlLang.writes s = false
/-- a statement that writes: outside a transaction it waits for the write lock (SQLITE_BUSY once busy_timeout runs out,
nothing changed), runs on the latest committed version and commits at once, all or nothing; inside one it runs on the
transaction's db; an error changes nothing -/
def SqliteWrite : Prop := db.ByEngine fun op => ∃ s, op = .stmt s ∧ Iso.sqlLang.writes s = true
/-- `commit`: the transaction's db becomes the next committed version, all at once, and the lock is freed; WAL: it
never waits -/
def SqliteCommit : Prop := db.ByEngine (· = .commit)
/-- `rollback`, and the process ending (exit or kill -9) in a transaction: the transaction's writes are discarded and
the lock is freed -/
def SqliteRollback : Prop := db.ByEngine fun op => op = .rollback ∨ op = .close

/-- all of them -/
structure SqliteSound : Prop where
  begin : SqliteBegin db
  read : SqliteRead db
  write : SqliteWrite db
  commit : SqliteCommit db
  rollback : SqliteRollback db

/-- a db that is the engine -/
def idealDb : Db where
  World := Iso.Eng Sql.DB (Sql.Stmt × List Sql.Val)
  view := id
  Does w c op r w' := ∃ t, Iso.step {} Iso.sqlLang w c op t = some (r, w')

/-- the assumptions hold together: the engine has them all -/
theorem sqlite_consistent : SqliteSound idealDb where
  begin _ _ _ _ _ _ h := h
  read _ _ _ _ _ _ h := h
  write _ _ _ _ _ _ h := h
  commit _ _ _ _ _ _ h := h
  rollback _ _ _ _ _ _ h := h

instance : Inhabited Db := ⟨idealDb⟩

/-- the swarm's db, as real sqlite runs it -/
opaque realDb : Db

/-- `begin immediate` (sqlite_spec: sqlite_begin) -/
axiom sqlite_begin : SqliteBegin realDb
/-- reads (sqlite_spec: sqlite_read) -/
axiom sqlite_read : SqliteRead realDb
/-- writes (sqlite_spec: sqlite_write) -/
axiom sqlite_write : SqliteWrite realDb
/-- `commit` (sqlite_spec: sqlite_commit) -/
axiom sqlite_commit : SqliteCommit realDb
/-- `rollback` and death (sqlite_spec: sqlite_rollback) -/
axiom sqlite_rollback : SqliteRollback realDb

end Swarm.Env
