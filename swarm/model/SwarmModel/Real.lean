import SwarmModel.Env
import SwarmModel.Decide

/-! What the Lua decides from the tools' answers is what the model decides on its view of the world, given `Env`'s
assumptions about `real`. Each decision is written as the Lua line it stands for; `check.sh` prints the assumptions
each theorem here rests on. -/

namespace Swarm.Env

variable {w : real.World}

/-- watchd.landed_ref(cwd, k, b): `merge-base --is-ancestor`, else the squash content check, else `gh` says a PR
from this branch merged at this head (`gh` is not modelled: its answer is a parameter) -/
def landedRef (t : Tools) (w : t.World) (k b : Nat) (gh : Bool) : Bool := t.isAncestor w k b || t.sameContent w k b || gh

/-- landed_ref saying "landed" means reachable, or `gh` said so -/
theorem landedRef_reach {k b : Nat} {gh : Bool} (h : landedRef real w k b gh = true) :
    (real.git w).reachFrom k b = true ∨ gh = true := by
  simp only [landedRef, Bool.or_eq_true] at h
  rcases h with (h | h) | h
  · exact .inl (ancestor_reach w k b h)
  · exact .inl (same_content_reach w k b h)
  · exact .inr h

/-- watchd.sweep_worktrees' gate for worktree x, on the tools' answers: listed, not `used` (a live agent's agent.wt
or cwd, or wt_map's pick: the db's answer, a parameter), no process inside, untouched for SWEEP_IDLE, `status
--porcelain` empty, and landed_ref of its HEAD on some protected ref (`gh b`: that ref's `gh` answer) -/
def sweepGate (t : Tools) (w : t.World) (c : Cfg) (used : Bool) (x : Nat) (gh : Nat → Bool) : Bool :=
  t.listed w x && !used && !t.cwdIn w x && !decide (t.now w < t.touched w x + sweepIdle) && t.statusClean w x &&
    c.bases.any fun b => landedRef t w ((t.git w).wt x).head b (gh b)

/-- With no `gh` answer, the Lua's sweep gate on the tools is the model's `sweeps` premise (W1's, `gcOk`) on its view:
the worktree is there, unused, has no process inside, isn't recent, is clean, and its HEAD is reachable from a
protected ref. -/
theorem sweepGate_W1 {c : Cfg} {used : Bool} {x : Nat} (h : sweepGate real w c used x (fun _ => false) = true) :
    let y := (real.git w).wt x
    y.on = true ∧ used = false ∧ y.proc = false ∧ y.recent = false ∧ y.dirty = false ∧ (real.git w).safe c y.head = true := by
  simp only [sweepGate, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hl, hu⟩, hp⟩, hr⟩, hs⟩, b, hb, hland⟩ := h
  have hon : ((real.git w).wt x).on = true := by rw [← listed_on w x]; exact hl
  refine ⟨hon, by simpa using hu, by rw [← cwds_proc w x]; simpa using hp, ?_, ?_, ?_⟩
  · rw [touched_recent w x]; simpa using hr
  · have := status_clean w x hon; rw [hs] at this; simpa using this.symm
  · simp only [Git.safe, List.any_eq_true]
    exact ⟨b, hb, (landedRef_reach hland).resolve_right (by simp)⟩

/-- `git worktree remove` of x touches no other worktree, no branch and no commit, and removes nothing dirty -/
theorem wtRemove_only {x : Nat} :
    let g := real.git w; let g' := real.git (real.wtRemove w x)
    g'.brs = g.brs ∧ g'.cm = g.cm ∧ (∀ y, y ≠ x → g'.wt y = g.wt y) ∧ ((g.wt x).dirty = true → g' = g) := by
  simp only [wt_remove w x]
  split
  · refine ⟨rfl, rfl, fun y hy => ?_, fun hd => by simp_all⟩
    simp only [Git.wt, Git.setWt, List.getD_eq_getElem?_getD, List.getElem?_modify]
    simp [Ne.symm hy]
  · exact ⟨rfl, rfl, fun _ _ => rfl, fun _ => rfl⟩

/-- delete_branch's guarded path, `update-ref -d refs/heads/b k`: if branch b went, its tip was k, the HEAD the sweep
checked, so the tip it deleted was reachable from a protected ref whenever k was; and no other branch went -/
theorem delRef_guarded {c : Cfg} {b k : Nat} (hk : (real.git w).safe c k = true)
    (hgone : real.git (real.delRef w b k) ≠ real.git w) :
    (real.git w).tip b = some k ∧ (real.git w).safe c ((real.git w).tipOf b) = true ∧
      ∀ b', b' ≠ b → (real.git (real.delRef w b k)).tip b' = (real.git w).tip b' := by
  rw [del_ref w b k] at hgone ⊢
  by_cases ht : (real.git w).tip b = some k
  · refine ⟨ht, by simp [Git.tipOf, ht, hk], fun b' hb' => ?_⟩
    rw [ite_eq_left ht]
    simp [Git.tip, Ne.symm hb']
  · simp [ht] at hgone

/-- W2 at the tools: end_agent's `hc kill` ends that terminal and leaves every worktree, branch and commit as it was -/
theorem endAgent_keepsGit {h : Nat} :
    real.termLive (real.hcKill w h) h = false ∧ Git.durable (real.git (real.hcKill w h)) = Git.durable (real.git w) :=
  ⟨(hc_kill_ends w h).1, (hc_kill_ends w h).2.2⟩

/-- reap (and `who`, `post`) read a bound row as gone exactly when its terminal is: `hc ls` lists it as live or not -/
theorem reap_gone {h : Nat} : real.hcLs w h = false ↔ real.termLive w h = false := by rw [hc_ls_live]

/-- lifecycle's and msgs' waiter check, `kill(waiter, 0) == 0`, is the waiter being alive -/
theorem waiter_alive {p : Nat} : real.kill0 w p = real.alive w p := kill0_alive w p

/-- reap's `lease_until < now` stays true once true: a lapsed lease never reads live again, so the model's `expire`
needs no inverse -/
theorem lapsed_stays {w' : real.World} {lease : Nat} (hl : lease < real.now w) (h : real.Later w w') :
    lease < real.now w' := Nat.lt_of_lt_of_le hl (now_mono w w' h)

/-! ## The real db (board #33): every run of it is a run of the engine, so `Iso.lean`'s theorems hold of it -/

/-- every op of the real db is an engine step -/
theorem realDb_step {w w' : realDb.World} {c : Nat} {op : Iso.Op (Sql.Stmt × List Sql.Val)} {r : Iso.Res Sql.Out}
    (h : realDb.Does w c op r w') : ∃ t, Iso.step {} Iso.sqlLang (realDb.view w) c op t = some (r, realDb.view w') := by
  cases op with
  | begin => exact sqlite_begin _ _ _ _ _ rfl h
  | stmt s =>
    cases hw : Iso.sqlLang.writes s
    · exact sqlite_read _ _ _ _ _ ⟨s, rfl, hw⟩ h
    · exact sqlite_write _ _ _ _ _ ⟨s, rfl, hw⟩ h
  | commit => exact sqlite_commit _ _ _ _ _ rfl h
  | rollback => exact sqlite_rollback _ _ _ _ _ (.inl rfl) h
  | close => exact sqlite_rollback _ _ _ _ _ (.inr rfl) h

/-- a run of the real db from a fresh one is a run of the engine -/
theorem realDb_reach {w0 w : realDb.World} {d0 : Sql.DB} (h0 : realDb.view w0 = Iso.Eng.init d0)
    (h : realDb.Run w0 w) : Iso.Reach {} Iso.sqlLang d0 (realDb.view w) := by
  induction h with
  | refl => exact h0 ▸ .init
  | step _ hd ih => obtain ⟨t, hs⟩ := realDb_step hd; exact .step ih hs

/-- the real db is serializable: every committed version is its transaction's statements run on the version before,
and a transaction holding the lock runs on the latest version -/
theorem real_serializable {w0 w : realDb.World} {d0 : Sql.DB} (h0 : realDb.view w0 = Iso.Eng.init d0)
    (h : realDb.Run w0 w) : Iso.Inv Iso.sqlLang (realDb.view w) :=
  Iso.serializable (realDb_reach h0 h)

/-- every statement answers on its transaction's db -/
theorem real_stmt_out {w w' : realDb.World} {c : Nat} {s : Sql.Stmt × List Sql.Val} {r : Except String Sql.Out}
    (h : realDb.Does w c (.stmt s) (.out r) w') : r = Iso.sqlLang.out s ((realDb.view w).view c) := by
  obtain ⟨t, hs⟩ := realDb_step h; exact Iso.stmt_out hs

/-- SQLITE_BUSY only after waiting out busy_timeout, with no transaction open, and nothing changed -/
theorem real_busyClean {w0 w w' : realDb.World} {d0 : Sql.DB} {c : Nat} {op : Iso.Op (Sql.Stmt × List Sql.Val)}
    {b : Bool} (h0 : realDb.view w0 = Iso.Eng.init d0) (h : realDb.Run w0 w) (hd : realDb.Does w c op (.busy b) w') :
    b = true ∧ (realDb.view w).mode c = .auto ∧ realDb.view w' = realDb.view w := by
  obtain ⟨t, hs⟩ := realDb_step hd
  exact Iso.busyClean_of rfl _ c op t b _ (realDb_reach h0 h) hs

/-- ci.pr_act on gh's answers for PR p (board #28) is its decision on the world's PR, which `Decide.prAct_lifted` shows is
the model's poll: k is task whose PR p is, as the model has it -/
theorem prAct_real {w : real.World} {p : Nat} {k : PrW.PTask} (hc : k.pr.checks = real.prChecks w p)
    (hm : k.pr.merged = real.prMerged w p) (gated told : Bool) :
    Decide.prActL { state := real.ghState w p, verdict := real.ghVerdict w p } gated told
      = Decide.prActL (Decide.prRow k) gated told := by
  rw [gh_checks w p, gh_state w p]
  simp [Decide.prRow, hc, hm]

end Swarm.Env
