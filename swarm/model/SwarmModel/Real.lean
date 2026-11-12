import SwarmModel.Env
import SwarmModel.Decide

/-! What the Lua decides from the tools' answers is what the model decides on its view of the world, given `Env`'s
assumptions. Each theorem is stated of any `Tools` (or `Db`) and takes the assumptions it uses as hypotheses (board #25:
a downstream proof can supply them for another machine, `ideal` say); the one of the same name without the `Tools.` or
`Db.` prefix is it for `real`, from Env.lean's axioms. Each decision is written as the Lua line it stands for;
`check.sh` prints the assumptions each theorem here rests on. -/

namespace Swarm.Env

/-- watchd.landed_ref(cwd, k, b): `merge-base --is-ancestor`, else the squash content check, else `gh` says a PR
from this branch merged at this head (`gh` is not modelled: its answer is a parameter) -/
def landedRef (t : Tools) (w : t.World) (k b : Nat) (gh : Bool) : Bool := t.isAncestor w k b || t.sameContent w k b || gh

/-- watchd.sweep_worktrees' gate for worktree x, on the tools' answers: listed, not `used` (a live agent's agent.wt
or cwd, or wt_map's pick: the db's answer, a parameter), no process inside, untouched for SWEEP_IDLE, `status
--porcelain` empty, and landed_ref of its HEAD on some protected ref (`gh b`: that ref's `gh` answer) -/
def sweepGate (t : Tools) (w : t.World) (c : Cfg) (used : Bool) (x : Nat) (gh : Nat → Bool) : Bool :=
  t.listed w x && !used && !t.cwdIn w x && !decide (t.now w < t.touched w x + sweepIdle) && t.statusClean w x &&
    c.bases.any fun b => landedRef t w ((t.git w).wt x).head b (gh b)

namespace Tools
variable {t : Tools} {w : t.World}

/-- landed_ref saying "landed" means reachable, or `gh` said so -/
theorem landedRef_reach (ha : AncestorReach t) (hsc : SameContentReach t) {k b : Nat} {gh : Bool}
    (h : landedRef t w k b gh = true) : (t.git w).reachFrom k b = true ∨ gh = true := by
  simp only [landedRef, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact .inl (ha w k b h)
  · exact .inl (hsc w k b h)
  · exact .inr h

/-- With no `gh` answer, the Lua's sweep gate on the tools is the model's `sweeps` premise (W1's, `gcOk`) on its view:
the worktree is there, unused, has no process inside, isn't recent, is clean, and its HEAD is reachable from a
protected ref. -/
theorem sweepGate_W1 (ha : AncestorReach t) (hsc : SameContentReach t) (hsl : StatusClean t) (hlo : ListedOn t)
    (hcp : CwdsProc t) (htr : TouchedRecent t) {c : Cfg} {used : Bool} {x : Nat}
    (h : sweepGate t w c used x (fun _ => false) = true) :
    let y := (t.git w).wt x
    y.on = true ∧ used = false ∧ y.proc = false ∧ y.recent = false ∧ y.dirty = false ∧ (t.git w).safe c y.head = true := by
  simp only [sweepGate, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hl, hu⟩, hp⟩, hr⟩, hs⟩, b, hb, hland⟩ := h
  have hon : ((t.git w).wt x).on = true := by rw [← hlo w x]; exact hl
  refine ⟨hon, by simpa using hu, by rw [← hcp w x]; simpa using hp, ?_, ?_, ?_⟩
  · rw [htr w x]; simpa using hr
  · have := hsl w x hon; rw [hs] at this; simpa using this.symm
  · simp only [Git.safe, List.any_eq_true]
    exact ⟨b, hb, (landedRef_reach ha hsc hland).resolve_right (by simp)⟩

/-- `git worktree remove` of x touches no other worktree, no branch and no commit, and removes nothing dirty -/
theorem wtRemove_only (hwr : WtRemove t) {x : Nat} :
    let g := t.git w; let g' := t.git (t.wtRemove w x)
    g'.brs = g.brs ∧ g'.cm = g.cm ∧ (∀ y, y ≠ x → g'.wt y = g.wt y) ∧ ((g.wt x).dirty = true → g' = g) := by
  simp only [hwr w x]
  split
  · refine ⟨rfl, rfl, fun y hy => ?_, fun hd => by simp_all⟩
    simp only [Git.wt, Git.setWt, List.getD_eq_getElem?_getD, List.getElem?_modify]
    simp [Ne.symm hy]
  · exact ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- delete_branch's guarded path, `update-ref -d refs/heads/b k`: if branch b went, its tip was k, the HEAD the sweep
checked, so the tip it deleted was reachable from a protected ref whenever k was; and no other branch went -/
theorem delRef_guarded (hdr : DelRef t) {c : Cfg} {b k : Nat} (hk : (t.git w).safe c k = true)
    (hgone : t.git (t.delRef w b k) ≠ t.git w) :
    (t.git w).tip b = some k ∧ (t.git w).safe c ((t.git w).tipOf b) = true ∧
      ∀ b', b' ≠ b → (t.git (t.delRef w b k)).tip b' = (t.git w).tip b' := by
  rw [hdr w b k] at hgone ⊢
  by_cases ht : (t.git w).tip b = some k
  · refine ⟨ht, by simp [Git.tipOf, ht, hk], fun b' hb' => ?_⟩
    rw [ite_eq_left ht]
    simp [Git.tip, Ne.symm hb']
  · simp [ht] at hgone

/-- R1 at the tools: `--restart`'s new watchd is as the model's `restart` makes it: right after `hc run --bg` its terminal
is listed live and `kill(pid, 0)` (run.pid_alive, what the restart and the old watchd's loop ask) finds the program,
the model's `World.alive` -/
theorem restart_alive (hr : HcRunStarts t) (hl : HcLsLive t) (hk : Kill0Alive t) (w : t.World) :
    t.hcLs (t.hcRun w) (t.hcRunAddr w) = true ∧ t.kill0 (t.hcRun w) (t.hcRunPid w) = true :=
  ⟨(hl _ _).trans (hr w).1, (hk _ _).trans (hr w).2⟩
/-- W2 at the tools: end_agent's `hc kill` ends that terminal and leaves every worktree, branch and commit as it was -/
theorem endAgent_keepsGit (hk : HcKillEnds t) {h : Nat} :
    t.termLive (t.hcKill w h) h = false ∧ Git.durable (t.git (t.hcKill w h)) = Git.durable (t.git w) :=
  ⟨(hk w h).1, (hk w h).2.2⟩

/-- reap (and `who`, `post`) read a bound row as gone exactly when its terminal is: `hc ls` lists it as live or not -/
theorem reap_gone (hl : HcLsLive t) {h : Nat} : t.hcLs w h = false ↔ t.termLive w h = false := by rw [hl]

/-- lifecycle's and msgs' waiter check, `kill(waiter, 0) == 0`, is the waiter being alive -/
theorem waiter_alive (hk : Kill0Alive t) {p : Nat} : t.kill0 w p = t.alive w p := hk w p

/-- reap's `lease_until < now` stays true once true: a lapsed lease never reads live again, so the model's `expire`
needs no inverse -/
theorem lapsed_stays (hn : NowMono t) {w' : t.World} {lease : Nat} (hl : lease < t.now w) (h : t.Later w w') :
    lease < t.now w' := Nat.lt_of_lt_of_le hl (hn w w' h)

/-- ci.pr_act on gh's answers for PR p (board #28) is its decision on the world's PR, which `Decide.prAct_lifted` shows is
the model's poll: k is task whose PR p is, as the model has it -/
theorem prAct (hgc : GhChecks t) (hgs : GhState t) {p : Nat} {k : PrW.PTask} (hc : k.pr.checks = t.prChecks w p)
    (hm : k.pr.merged = t.prMerged w p) (gated told : Bool) :
    Decide.prActL { state := t.ghState w p, verdict := t.ghVerdict w p } gated told
      = Decide.prActL (Decide.prRow k) gated told := by
  rw [hgc w p, hgs w p]
  simp [Decide.prRow, hc, hm]

end Tools

/-! ## Any db with sqlite's assumptions (board #33): every run of it is a run of the engine, so `Iso.lean`'s theorems
hold of it -/

namespace Db
variable {db : Db}

/-- every op of the db is an engine step -/
theorem engine_step (hdb : SqliteSound db) {w w' : db.World} {c : Nat} {op : Iso.Op (Sql.Stmt × List Sql.Val)}
    {r : Iso.Res Sql.Out} (h : db.Does w c op r w') :
    ∃ t, Iso.step {} Iso.sqlLang (db.view w) c op t = some (r, db.view w') := by
  cases op with
  | begin => exact hdb.begin _ _ _ _ _ rfl h
  | stmt s =>
    cases hw : Iso.sqlLang.writes s
    · exact hdb.read _ _ _ _ _ ⟨s, rfl, hw⟩ h
    · exact hdb.write _ _ _ _ _ ⟨s, rfl, hw⟩ h
  | commit => exact hdb.commit _ _ _ _ _ rfl h
  | rollback => exact hdb.rollback _ _ _ _ _ (.inl rfl) h
  | close => exact hdb.rollback _ _ _ _ _ (.inr rfl) h

/-- a run of the db from a fresh one is a run of the engine -/
theorem engine_reach (hdb : SqliteSound db) {w0 w : db.World} {d0 : Sql.DB} (h0 : db.view w0 = Iso.Eng.init d0)
    (h : db.Run w0 w) : Iso.Reach {} Iso.sqlLang d0 (db.view w) := by
  induction h with
  | refl => exact h0 ▸ .init
  | step _ hd ih => obtain ⟨t, hs⟩ := engine_step hdb hd; exact .step ih hs

/-- the db is serializable: every committed version is its transaction's statements run on the version before, and a
transaction holding the lock runs on the latest version -/
theorem serializable (hdb : SqliteSound db) {w0 w : db.World} {d0 : Sql.DB} (h0 : db.view w0 = Iso.Eng.init d0)
    (h : db.Run w0 w) : Iso.Inv Iso.sqlLang (db.view w) :=
  Iso.serializable (engine_reach hdb h0 h)

/-- every statement answers on its transaction's db -/
theorem stmt_out (hdb : SqliteSound db) {w w' : db.World} {c : Nat} {s : Sql.Stmt × List Sql.Val}
    {r : Except String Sql.Out} (h : db.Does w c (.stmt s) (.out r) w') : r = Iso.sqlLang.out s ((db.view w).view c) := by
  obtain ⟨t, hs⟩ := engine_step hdb h; exact Iso.stmt_out hs

/-- SQLITE_BUSY only after waiting out busy_timeout, with no transaction open, and nothing changed -/
theorem busyClean (hdb : SqliteSound db) {w0 w w' : db.World} {d0 : Sql.DB} {c : Nat}
    {op : Iso.Op (Sql.Stmt × List Sql.Val)} {b : Bool} (h0 : db.view w0 = Iso.Eng.init d0) (h : db.Run w0 w)
    (hd : db.Does w c op (.busy b) w') : b = true ∧ (db.view w).mode c = .auto ∧ db.view w' = db.view w := by
  obtain ⟨t, hs⟩ := engine_step hdb hd
  exact Iso.busyClean_of rfl _ c op t b _ (engine_reach hdb h0 h) hs

end Db

/-! ## The same, for `real` and `realDb`, from Env.lean's axioms -/

/-- sqlite's assumptions, of the real db -/
theorem realDb_sound : SqliteSound realDb := ⟨sqlite_begin, sqlite_read, sqlite_write, sqlite_commit, sqlite_rollback⟩

variable {w : real.World}

theorem landedRef_reach {k b : Nat} {gh : Bool} (h : landedRef real w k b gh = true) :
    (real.git w).reachFrom k b = true ∨ gh = true := Tools.landedRef_reach ancestor_reach same_content_reach h
theorem sweepGate_W1 {c : Cfg} {used : Bool} {x : Nat} (h : sweepGate real w c used x (fun _ => false) = true) :
    let y := (real.git w).wt x
    y.on = true ∧ used = false ∧ y.proc = false ∧ y.recent = false ∧ y.dirty = false ∧ (real.git w).safe c y.head = true :=
  Tools.sweepGate_W1 ancestor_reach same_content_reach status_clean listed_on cwds_proc touched_recent h
theorem wtRemove_only {x : Nat} :
    let g := real.git w; let g' := real.git (real.wtRemove w x)
    g'.brs = g.brs ∧ g'.cm = g.cm ∧ (∀ y, y ≠ x → g'.wt y = g.wt y) ∧ ((g.wt x).dirty = true → g' = g) :=
  Tools.wtRemove_only wt_remove
theorem delRef_guarded {c : Cfg} {b k : Nat} (hk : (real.git w).safe c k = true)
    (hgone : real.git (real.delRef w b k) ≠ real.git w) :
    (real.git w).tip b = some k ∧ (real.git w).safe c ((real.git w).tipOf b) = true ∧
      ∀ b', b' ≠ b → (real.git (real.delRef w b k)).tip b' = (real.git w).tip b' :=
  Tools.delRef_guarded del_ref hk hgone
theorem restart_alive : real.hcLs (real.hcRun w) (real.hcRunAddr w) = true ∧ real.kill0 (real.hcRun w) (real.hcRunPid w) = true :=
  Tools.restart_alive hc_run_starts hc_ls_live kill0_alive w
theorem endAgent_keepsGit {h : Nat} :
    real.termLive (real.hcKill w h) h = false ∧ Git.durable (real.git (real.hcKill w h)) = Git.durable (real.git w) :=
  Tools.endAgent_keepsGit hc_kill_ends
theorem reap_gone {h : Nat} : real.hcLs w h = false ↔ real.termLive w h = false := Tools.reap_gone hc_ls_live
theorem waiter_alive {p : Nat} : real.kill0 w p = real.alive w p := Tools.waiter_alive kill0_alive
theorem lapsed_stays {w' : real.World} {lease : Nat} (hl : lease < real.now w) (h : real.Later w w') :
    lease < real.now w' := Tools.lapsed_stays now_mono hl h
theorem prAct_real {p : Nat} {k : PrW.PTask} (hc : k.pr.checks = real.prChecks w p)
    (hm : k.pr.merged = real.prMerged w p) (gated told : Bool) :
    Decide.prActL { state := real.ghState w p, verdict := real.ghVerdict w p } gated told
      = Decide.prActL (Decide.prRow k) gated told := Tools.prAct gh_checks gh_state hc hm gated told

theorem realDb_step {w w' : realDb.World} {c : Nat} {op : Iso.Op (Sql.Stmt × List Sql.Val)} {r : Iso.Res Sql.Out}
    (h : realDb.Does w c op r w') : ∃ t, Iso.step {} Iso.sqlLang (realDb.view w) c op t = some (r, realDb.view w') :=
  Db.engine_step realDb_sound h
theorem realDb_reach {w0 w : realDb.World} {d0 : Sql.DB} (h0 : realDb.view w0 = Iso.Eng.init d0)
    (h : realDb.Run w0 w) : Iso.Reach {} Iso.sqlLang d0 (realDb.view w) := Db.engine_reach realDb_sound h0 h
theorem real_serializable {w0 w : realDb.World} {d0 : Sql.DB} (h0 : realDb.view w0 = Iso.Eng.init d0)
    (h : realDb.Run w0 w) : Iso.Inv Iso.sqlLang (realDb.view w) := Db.serializable realDb_sound h0 h
theorem real_stmt_out {w w' : realDb.World} {c : Nat} {s : Sql.Stmt × List Sql.Val} {r : Except String Sql.Out}
    (h : realDb.Does w c (.stmt s) (.out r) w') : r = Iso.sqlLang.out s ((realDb.view w).view c) :=
  Db.stmt_out realDb_sound h
theorem real_busyClean {w0 w w' : realDb.World} {d0 : Sql.DB} {c : Nat} {op : Iso.Op (Sql.Stmt × List Sql.Val)}
    {b : Bool} (h0 : realDb.view w0 = Iso.Eng.init d0) (h : realDb.Run w0 w) (hd : realDb.Does w c op (.busy b) w') :
    b = true ∧ (realDb.view w).mode c = .auto ∧ realDb.view w' = realDb.view w := Db.busyClean realDb_sound h0 h hd

end Swarm.Env
