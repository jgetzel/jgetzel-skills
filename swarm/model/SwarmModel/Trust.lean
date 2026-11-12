import SwarmModel.Real
import SwarmModel.Nudge

/-! Each hypothesis a theorem keeps is needed (board #68): for each theorem of `Real.lean` (and `Nudge.lean`'s
`Tools.N1'`; `Contract.lean` restates them) and each environment hypothesis it takes, a machine that has every other
hypothesis of that theorem, where the guarantee fails. The pattern is Findings.lean's: a switch off (here: one tool
lying), the property refuted. The tools machines are `ideal` with one tool changed to lie; the dbs are the engine with
one kind of op broken (`broken`). -/

namespace Swarm.Env.Trust
open Env

/-- the ideal machine's assumptions, one by one (`consistent`) -/
theorem i_a : AncestorReach ideal := consistent.1
theorem i_sc : SameContentReach ideal := consistent.2.1
theorem i_sl : StatusClean ideal := consistent.2.2.1
theorem i_lo : ListedOn ideal := consistent.2.2.2.1
theorem i_ls : HcLsShows ideal := consistent.2.2.2.2.2.2.2.1
theorem i_hr : HcRunStarts ideal := consistent.2.2.2.2.2.2.2.2.2.2.1
theorem i_kf : Kill0Finds ideal := consistent.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem i_cp : CwdsProc ideal := consistent.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem i_tr : TouchedRecent ideal := consistent.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem i_gc : GhChecks ideal := consistent.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem i_gs : GhState ideal := consistent.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- worktrees `ws`; base 0 at commit 0, branch 1 at commit 1, which base 0 doesn't hold; no terminal, no process -/
def wd (ws : List Wt) : IdealWorld :=
  { git := { wts := ws, brs := [some 0, some 1], cm := [⟨[0], [0]⟩, ⟨[1], [1]⟩] }, terms := fun _ => false,
    inputs := fun _ => [], procs := fun _ => false, clock := 0, checks := fun _ => .pending, merged := fun _ => false }
/-- worktree 0: there, clean, no process inside, untouched, HEAD k -/
def wt0 (k : Nat) : Wt := { (default : Wt) with on := true, head := k }

/-! ## landed_ref -/

/-- `Tools.landedRef_reach`'s statement, of t -/
def LandedReach (t : Tools) : Prop :=
  ∀ (w : t.World) k b gh, landedRef t w k b gh = true → (t.git w).reachFrom k b = true ∨ gh = true

theorem need_landedRef_ancestor :
    ∃ t, SameContentReach t ∧ ¬ LandedReach t :=
  ⟨{ ideal with isAncestor := fun _ _ _ => true }, i_sc, fun h => absurd (h (wd []) 1 0 false rfl) (by decide)⟩
theorem need_landedRef_sameContent :
    ∃ t, AncestorReach t ∧ ¬ LandedReach t :=
  ⟨{ ideal with sameContent := fun _ _ _ => true }, i_a, fun h => absurd (h (wd []) 1 0 false rfl) (by decide)⟩

/-! ## the sweep's gate -/

/-- `Tools.sweepGate_W1`'s statement, of t -/
def GateW1 (t : Tools) : Prop :=
  ∀ (w : t.World) (c : Cfg) used x, sweepGate t w c used x (fun _ => false) = true →
    ((t.git w).wt x).on = true ∧ used = false ∧ ((t.git w).wt x).proc = false ∧ ((t.git w).wt x).recent = false ∧
      ((t.git w).wt x).dirty = false ∧ (t.git w).safe c ((t.git w).wt x).head = true

theorem need_sweep_ancestor : ∃ t, SameContentReach t ∧ StatusClean t ∧ ListedOn t ∧ CwdsProc t ∧ TouchedRecent t ∧
    ¬ GateW1 t :=
  ⟨{ ideal with isAncestor := fun _ _ _ => true }, i_sc, i_sl, i_lo, i_cp, i_tr,
   fun h => absurd (h (wd [wt0 1]) {} false 0 (by decide)) (by decide)⟩
theorem need_sweep_sameContent : ∃ t, AncestorReach t ∧ StatusClean t ∧ ListedOn t ∧ CwdsProc t ∧ TouchedRecent t ∧
    ¬ GateW1 t :=
  ⟨{ ideal with sameContent := fun _ _ _ => true }, i_a, i_sl, i_lo, i_cp, i_tr,
   fun h => absurd (h (wd [wt0 1]) {} false 0 (by decide)) (by decide)⟩
/-- `status` says clean of a dirty worktree -/
theorem need_sweep_statusClean : ∃ t, AncestorReach t ∧ SameContentReach t ∧ ListedOn t ∧ CwdsProc t ∧
    TouchedRecent t ∧ ¬ GateW1 t :=
  ⟨{ ideal with statusClean := fun _ _ => true }, i_a, i_sc, i_lo, i_cp, i_tr,
   fun h => absurd (h (wd [{ wt0 0 with dirty := true }]) {} false 0 (by decide)) (by decide)⟩
/-- `worktree list` lists a worktree that isn't there -/
theorem need_sweep_listedOn : ∃ t, AncestorReach t ∧ SameContentReach t ∧ StatusClean t ∧ CwdsProc t ∧
    TouchedRecent t ∧ ¬ GateW1 t :=
  ⟨{ ideal with listed := fun _ _ => true }, i_a, i_sc, i_sl, i_cp, i_tr,
   fun h => absurd (h (wd []) {} false 0 (by decide)) (by decide)⟩
/-- `machine.cwds()` misses a process inside -/
theorem need_sweep_cwdsProc : ∃ t, AncestorReach t ∧ SameContentReach t ∧ StatusClean t ∧ ListedOn t ∧
    TouchedRecent t ∧ ¬ GateW1 t :=
  ⟨{ ideal with cwdIn := fun _ _ => false }, i_a, i_sc, i_sl, i_lo, i_tr,
   fun h => absurd (h (wd [{ wt0 0 with proc := true }]) {} false 0 (by decide)) (by decide)⟩
/-- the mtimes read old of a worktree touched just now -/
theorem need_sweep_touchedRecent : ∃ t, AncestorReach t ∧ SameContentReach t ∧ StatusClean t ∧ ListedOn t ∧
    CwdsProc t ∧ ¬ GateW1 t :=
  ⟨{ ideal with touched := fun _ _ => 0 }, i_a, i_sc, i_sl, i_lo, i_cp,
   fun h => absurd (h (wd [{ wt0 0 with recent := true }]) {} false 0 (by decide)) (by decide)⟩

/-! ## git's writes -/

/-- `worktree remove` that deletes every branch -/
theorem need_wtRemove : ¬ ∀ (w : IdealWorld) x,
    let t : Tools := { ideal with wtRemove := fun w _ => { w with git := { w.git with brs := [] } } }
    (t.git (t.wtRemove w x)).brs = (t.git w).brs :=
  fun h => absurd (h (wd []) 0) (by decide)

/-- `update-ref -d` that deletes the branch whatever its tip -/
theorem need_delRef : ¬ ∀ (w : IdealWorld) (c : Cfg) b k,
    let t : Tools := { ideal with delRef := fun w b _ => { w with git := { w.git with brs := w.git.brs.set b none } } }
    (t.git w).safe c k = true → t.git (t.delRef w b k) ≠ t.git w → (t.git w).tip b = some k :=
  fun h => absurd (h (wd []) {} 1 0 (by decide) (by decide)) (by decide)

/-! ## hc and processes -/

/-- `Tools.restart_alive`'s statement, of t -/
def RestartAlive (t : Tools) : Prop :=
  ∀ w, t.hcLs (t.hcRun w) (t.hcRunAddr w) = true ∧ t.kill0 (t.hcRun w) (t.hcRunPid w) = true

/-- `hc run --bg` that starts nothing -/
theorem need_restart_hcRun : ∃ t, HcLsShows t ∧ Kill0Finds t ∧ ¬ RestartAlive t :=
  ⟨{ ideal with hcRun := id }, i_ls, i_kf, fun h => absurd (h (wd [])).1 (by decide)⟩
/-- `hc ls` that lists nothing -/
theorem need_restart_hcLs : ∃ t, HcRunStarts t ∧ Kill0Finds t ∧ ¬ RestartAlive t :=
  ⟨{ ideal with hcLs := fun _ _ => false }, i_hr, i_kf, fun h => absurd (h (wd [])).1 (by decide)⟩
/-- `kill(p, 0)` that finds nothing -/
theorem need_restart_kill0 : ∃ t, HcRunStarts t ∧ HcLsShows t ∧ ¬ RestartAlive t :=
  ⟨{ ideal with kill0 := fun _ _ => false }, i_hr, i_ls, fun h => absurd (h (wd [])).2 (by decide)⟩

/-- `hc kill` that kills nothing -/
theorem need_hcKill : ¬ ∀ (w : IdealWorld) h,
    let t : Tools := { ideal with hcKill := fun w _ => w }
    t.termLive (t.hcKill w h) h = false :=
  fun h => absurd (h { wd [] with terms := fun _ => true } 0) (by decide)

/-- `hc ls` that lists every terminal live -/
theorem need_hcLsLive : ¬ ∀ (w : IdealWorld) h,
    let t : Tools := { ideal with hcLs := fun _ _ => true }
    (t.hcLs w h = false ↔ t.termLive w h = false) :=
  fun h => absurd (h (wd []) 0) (by decide)

/-- `kill(p, 0)` that finds every pid -/
theorem need_kill0Alive : ¬ ∀ (w : IdealWorld) p,
    let t : Tools := { ideal with kill0 := fun _ _ => true }
    t.kill0 w p = t.alive w p :=
  fun h => absurd (h (wd []) 0) (by decide)

/-- `hc send` that types nothing -/
theorem need_hcSend : ¬ ∀ (w : IdealWorld) hT l,
    let t : Tools := { ideal with hcSend := fun w _ _ => w }
    t.termLive w hT = true → t.typed (t.hcSend w hT l) hT = t.typed w hT ++ [l] :=
  fun h => absurd (h { wd [] with terms := fun _ => true } 0 "" rfl) (by decide)

/-- and the nudge step that `Tools.N1'` pairs it with exists: agent 0 of the default `Cfg`'s first state -/
theorem nudge_enabled : (step {} (init {}) (.hnudge 0)).isSome = true := by rw [hnudge_enabled]; decide

/-! ## the clock -/

/-- a clock that steps back: a lapsed lease reads live again -/
theorem need_nowMono : ¬ ∀ (w w' : IdealWorld) lease,
    let t : Tools := { ideal with Later := fun _ _ => True }
    lease < t.now w → t.Later w w' → lease < t.now w' :=
  fun h => absurd (h { wd [] with clock := 1 } (wd []) sweepIdle (by decide) trivial) (by decide)

/-! ## gh -/

/-- `Tools.prAct`'s statement, of t -/
def PrActEq (t : Tools) : Prop :=
  ∀ (w : t.World) p (k : PrW.PTask), k.pr.checks = t.prChecks w p → k.pr.merged = t.prMerged w p → ∀ gated told,
    Decide.prActL { state := t.ghState w p, verdict := t.ghVerdict w p } gated told = Decide.prActL (Decide.prRow k) gated told

/-- gh says green of pending checks: a pr-gated agent is woken early -/
theorem need_prAct_checks : ∃ t, GhState t ∧ ¬ PrActEq t :=
  ⟨{ ideal with ghVerdict := fun _ _ => "green" }, i_gs, fun h => absurd (h (wd []) 0 {} rfl rfl true false) (by decide)⟩
/-- gh says merged of an open PR: its task is done early -/
theorem need_prAct_state : ∃ t, GhChecks t ∧ ¬ PrActEq t :=
  ⟨{ ideal with ghState := fun _ _ => "MERGED" }, i_gc, fun h => absurd (h (wd []) 0 {} rfl rfl false false) (by decide)⟩

/-! ## sqlite: the engine with one kind of op broken -/

abbrev SOp := Iso.Op (Sql.Stmt × List Sql.Val)

/-- the engine, but an op of kind K answers anything and leaves `bad` -/
def broken (K : SOp → Prop) (bad : Iso.Eng Sql.DB (Sql.Stmt × List Sql.Val)) : Db where
  World := Iso.Eng Sql.DB (Sql.Stmt × List Sql.Val)
  view := id
  Does w c op r w' := (K op ∧ w' = bad) ∨ (¬ K op ∧ ∃ t, Iso.step {} Iso.sqlLang w c op t = some (r, w'))

/-- kinds other than K still do what the engine does -/
theorem broken_by {K j : SOp → Prop} {bad} (hj : ∀ op, j op → ¬ K op) : (broken K bad).ByEngine j :=
  fun _ _ op _ _ hjo hd => hd.elim (fun h => absurd h.1 (hj op hjo)) (fun h => h.2)

def kBegin (op : SOp) : Prop := op = .begin
def kRead (op : SOp) : Prop := ∃ s, op = .stmt s ∧ Iso.sqlLang.writes s = false
def kWrite (op : SOp) : Prop := ∃ s, op = .stmt s ∧ Iso.sqlLang.writes s = true
def kCommit (op : SOp) : Prop := op = .commit
def kRollback (op : SOp) : Prop := op = .rollback ∨ op = .close

/-- a lock held by a connection with no transaction: not serializable's invariant -/
def bad : Iso.Eng Sql.DB (Sql.Stmt × List Sql.Val) := { Iso.Eng.init [] with lock := some 1 }
theorem bad_not_inv : ¬ Iso.Inv Iso.sqlLang bad := fun hi => by
  obtain ⟨v, d, u, h⟩ := hi.locked 1 rfl
  simp [bad, Iso.Eng.init] at h

/-- `Db.serializable`'s statement, of db -/
def Serial (db : Db) : Prop := ∀ (w0 w : db.World) d0, db.view w0 = Iso.Eng.init d0 → db.Run w0 w → Iso.Inv Iso.sqlLang (db.view w)
/-- `Db.busyClean`'s statement, of db -/
def BusyCleanDb (db : Db) : Prop := ∀ (w0 w w' : db.World) d0 c op b, db.view w0 = Iso.Eng.init d0 → db.Run w0 w →
  db.Does w c op (.busy b) w' → b = true ∧ (db.view w).mode c = .auto ∧ db.view w' = db.view w
/-- `Db.stmt_out`'s statement, of db -/
def StmtOut (db : Db) : Prop := ∀ (w w' : db.World) c s r, db.Does w c (.stmt s) (.out r) w' →
  r = Iso.sqlLang.out s ((db.view w).view c)

/-- an op of kind K exists: serializability and busyClean fail on the db broken at K -/
theorem broken_fails {K : SOp → Prop} {op : SOp} (hk : K op) : ¬ Serial (broken K bad) ∧ ¬ BusyCleanDb (broken K bad) :=
  ⟨fun h => bad_not_inv (h (Iso.Eng.init []) bad [] rfl (.step (r := .ok) (c := 0) .refl (.inl ⟨hk, rfl⟩))),
   fun h => absurd (h (Iso.Eng.init []) (Iso.Eng.init []) bad [] 0 op false rfl .refl (.inl ⟨hk, rfl⟩)).1 (by simp)⟩

def rd : Sql.Stmt × List Sql.Val := (.journal "wal", [])
def wr : Sql.Stmt × List Sql.Val := (.createIndex, [])

/-- a statement of kind K answers what its db doesn't: stmt_out fails on the db broken at K -/
theorem broken_out {K : SOp → Prop} {s} (hk : K (.stmt s)) : ¬ StmtOut (broken K bad) := fun h => by
  let x := Iso.sqlLang.out s ((Iso.Eng.init [] : Iso.Eng Sql.DB (Sql.Stmt × List Sql.Val)).view 0)
  by_cases e : x = .error "a"
  · exact absurd ((h (Iso.Eng.init []) bad 0 s (.error "b") (.inl ⟨hk, rfl⟩)).trans e) (by simp)
  · exact e (h (Iso.Eng.init []) bad 0 s (.error "a") (.inl ⟨hk, rfl⟩)).symm

theorem kBegin_only : ∀ op, kRead op ∨ kWrite op ∨ kCommit op ∨ kRollback op → ¬ kBegin op := by
  rintro _ (⟨s, rfl, _⟩ | ⟨s, rfl, _⟩ | rfl | rfl | rfl) h <;> cases h
theorem kRead_only : ∀ op, kBegin op ∨ kWrite op ∨ kCommit op ∨ kRollback op → ¬ kRead op := by
  rintro _ (rfl | ⟨s, rfl, hs⟩ | rfl | rfl | rfl) ⟨s', h, hs'⟩ <;> cases h
  simp_all
theorem kWrite_only : ∀ op, kBegin op ∨ kRead op ∨ kCommit op ∨ kRollback op → ¬ kWrite op := by
  rintro _ (rfl | ⟨s, rfl, hs⟩ | rfl | rfl | rfl) ⟨s', h, hs'⟩ <;> cases h
  simp_all
theorem kCommit_only : ∀ op, kBegin op ∨ kRead op ∨ kWrite op ∨ kRollback op → ¬ kCommit op := by
  rintro _ (rfl | ⟨s, rfl, _⟩ | ⟨s, rfl, _⟩ | rfl | rfl) h <;> cases h
theorem kRollback_only : ∀ op, kBegin op ∨ kRead op ∨ kWrite op ∨ kCommit op → ¬ kRollback op := by
  rintro _ (rfl | ⟨s, rfl, _⟩ | ⟨s, rfl, _⟩ | rfl) (h | h) <;> cases h

/-- `begin` broken: the other four hold, and serializability and busyClean fail -/
theorem need_db_begin : ∃ db, SqliteRead db ∧ SqliteWrite db ∧ SqliteCommit db ∧ SqliteRollback db ∧
    ¬ Serial db ∧ ¬ BusyCleanDb db :=
  ⟨broken kBegin bad, broken_by fun op h => kBegin_only op (.inl h), broken_by fun op h => kBegin_only op (.inr (.inl h)),
   broken_by fun op h => kBegin_only op (.inr (.inr (.inl h))), broken_by fun op h => kBegin_only op (.inr (.inr (.inr h))),
   broken_fails (op := .begin) rfl⟩
/-- a read broken: the other four hold, and serializability, busyClean and stmt_out fail -/
theorem need_db_read : ∃ db, SqliteBegin db ∧ SqliteWrite db ∧ SqliteCommit db ∧ SqliteRollback db ∧
    ¬ Serial db ∧ ¬ BusyCleanDb db ∧ ¬ StmtOut db :=
  have hk : kRead (.stmt rd) := ⟨rd, rfl, rfl⟩
  ⟨broken kRead bad, broken_by fun op h => kRead_only op (.inl h), broken_by fun op h => kRead_only op (.inr (.inl h)),
   broken_by fun op h => kRead_only op (.inr (.inr (.inl h))), broken_by fun op h => kRead_only op (.inr (.inr (.inr h))),
   (broken_fails hk).1, (broken_fails hk).2, broken_out hk⟩
/-- a write broken: the other four hold, and serializability, busyClean and stmt_out fail -/
theorem need_db_write : ∃ db, SqliteBegin db ∧ SqliteRead db ∧ SqliteCommit db ∧ SqliteRollback db ∧
    ¬ Serial db ∧ ¬ BusyCleanDb db ∧ ¬ StmtOut db :=
  have hk : kWrite (.stmt wr) := ⟨wr, rfl, rfl⟩
  ⟨broken kWrite bad, broken_by fun op h => kWrite_only op (.inl h), broken_by fun op h => kWrite_only op (.inr (.inl h)),
   broken_by fun op h => kWrite_only op (.inr (.inr (.inl h))), broken_by fun op h => kWrite_only op (.inr (.inr (.inr h))),
   (broken_fails hk).1, (broken_fails hk).2, broken_out hk⟩
/-- `commit` broken: the other four hold, and serializability and busyClean fail -/
theorem need_db_commit : ∃ db, SqliteBegin db ∧ SqliteRead db ∧ SqliteWrite db ∧ SqliteRollback db ∧
    ¬ Serial db ∧ ¬ BusyCleanDb db :=
  ⟨broken kCommit bad, broken_by fun op h => kCommit_only op (.inl h), broken_by fun op h => kCommit_only op (.inr (.inl h)),
   broken_by fun op h => kCommit_only op (.inr (.inr (.inl h))), broken_by fun op h => kCommit_only op (.inr (.inr (.inr h))),
   broken_fails (op := .commit) rfl⟩
/-- `rollback` and death broken: the other four hold, and serializability and busyClean fail -/
theorem need_db_rollback : ∃ db, SqliteBegin db ∧ SqliteRead db ∧ SqliteWrite db ∧ SqliteCommit db ∧
    ¬ Serial db ∧ ¬ BusyCleanDb db :=
  ⟨broken kRollback bad, broken_by fun op h => kRollback_only op (.inl h),
   broken_by fun op h => kRollback_only op (.inr (.inl h)), broken_by fun op h => kRollback_only op (.inr (.inr (.inl h))),
   broken_by fun op h => kRollback_only op (.inr (.inr (.inr h))), broken_fails (op := .rollback) (.inl rfl)⟩

/-! ## the statements above are the theorems': each holds given its hypotheses -/

example (t : Tools) (ha : AncestorReach t) (hsc : SameContentReach t) : LandedReach t :=
  fun _ _ _ _ h => Tools.landedRef_reach ha hsc h
example (t : Tools) (ha : AncestorReach t) (hsc : SameContentReach t) (hsl : StatusClean t) (hlo : ListedOn t)
    (hcp : CwdsProc t) (htr : TouchedRecent t) : GateW1 t :=
  fun _ _ _ _ h => Tools.sweepGate_W1 ha hsc hsl hlo hcp htr h
example (t : Tools) (hr : HcRunStarts t) (hl : HcLsShows t) (hk : Kill0Finds t) : RestartAlive t :=
  Tools.restart_alive hr hl hk
example (t : Tools) (hgc : GhChecks t) (hgs : GhState t) : PrActEq t :=
  fun _ _ _ hc hm g o => Tools.prAct hgc hgs hc hm g o
example (db : Db) (hb : SqliteBegin db) (hr : SqliteRead db) (hw : SqliteWrite db) (hc : SqliteCommit db)
    (hrb : SqliteRollback db) : Serial db ∧ BusyCleanDb db :=
  ⟨fun _ _ _ h0 h => Db.serializable hb hr hw hc hrb h0 h, fun _ _ _ _ _ _ _ h0 h hd => Db.busyClean hb hr hw hc hrb h0 h hd⟩
example (db : Db) (hr : SqliteRead db) (hw : SqliteWrite db) : StmtOut db :=
  fun _ _ _ _ _ h => Db.stmt_out hr hw h

end Swarm.Env.Trust
