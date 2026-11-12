import SwarmModel.NoWorkLost
import SwarmModel.Away

/-! A tick an error ends partway (board #84). `tickCut` is the tick with each pass stopped after any prefix of its units,
each unit a commit of its own (`Cut`); `Reachable` takes it as a third way to move, so S1-S5, W4, L3's invariant and
every invariant of reachable states hold of what a failed tick leaves. Here: N1, W1 and W2 of a cut tick; Q1 of a cut
tick whose notice pass ran; and what `passGuard` (a pcall per pass in watchd_tick) buys: with it a failing pass stops no
other pass (`passesIndep_of`), without it the first unit of reap failing stops the whole tick (finding #36). -/

namespace Swarm

theorem tickCut_all (c : Cfg) (s : State) : tickCut c ⟨none, none, none, none⟩ s = tickOf c s := rfl

@[simp] theorem reapCut_ag (c : Cfg) (o : Option Nat) (s : State) : (reapCut c o s).ag = s.ag := by
  cases o with
  | none => simp [reapCut]
  | some n => exact (foldl_inv (reapTask c) (fun x : State => x.ag = s.ag) _ _ rfl (fun b a h => by rw [reapTask_ag]; exact h))
@[simp] theorem tickCut_agt (c : Cfg) (k : Cut) (s : State) (a : Nat) :
    (tickCut c k s).agt a = (lifecycleCut c k.life (reapCut c k.reap s)).agt a := by
  simp [tickCut, State.agt]
@[simp] theorem tickCut_tk (c : Cfg) (k : Cut) (s : State) (t : Nat) :
    (tickCut c k s).tk t = (lifecycleCut c k.life (reapCut c k.reap s)).tk t := by
  simp [tickCut, State.tk]

/-- what each unit of lifecycle keeps, lifecycle cut anywhere keeps -/
theorem lifecycleCut_inv {c : Cfg} {z : State} (P : State → Prop)
    (hE : ∀ y b, P y → P (if finished c z b && !reusable c z b then endAgent y b else y))
    (hD : ∀ y b, P y → P (if reusable c z b && !(pool c z).all (y.agt b).told.contains then
      post (setAg y b fun g => { g with told := pool c z ++ g.told }) ⟨none, b, false, .digest, 0⟩ else y))
    (hS : ∀ y u, P y → P (spawnFor c (pool c z) y u)) (o : Option Nat) (hz : P z) : P (lifecycleCut c o z) := by
  unfold lifecycleCut; simp only []
  split
  · exact foldl_inv _ P _ _ (foldl_inv _ P _ _ hz hE) hD
  · exact foldl_inv _ P _ _ (foldl_inv _ P _ _ (foldl_inv _ P _ _ hz hE) hD) hS

/-- `lifecycle_keeps` of a cut lifecycle -/
theorem lifecycleCut_keeps {c : Cfg} {z : State} {a : Nat} (hf : finished c z a = false) (hl : (z.agt a).live = true)
    (o : Option Nat) : { (lifecycleCut c o z).agt a with told := [] } = { z.agt a with told := [] } :=
  (lifecycleCut_inv (fun y => { y.agt a with told := [] } = { z.agt a with told := [] } ∧ (y.agt a).live = true)
    (fun y b hy => by
      split
      · rename_i hh
        have hb : b ≠ a := by rintro rfl; simp [hf] at hh
        rw [endAgent_agt_ne hb.symm]; exact hy
      · exact hy)
    (fun y b hy => by
      split
      · simp only [post_agt, agt_setAg]; split
        · exact hy
        · exact hy
      · exact hy)
    (fun y u hy => by
      rcases spawnFor_agt c (pool c z) y u a with e | ⟨hn, _⟩
      · rw [e]; exact hy
      · have := nextAgent_not_live hn; rw [hy.2] at this; cases this)
    o ⟨rfl, hl⟩).1

/-- `lifecycle_tk` of a cut lifecycle -/
theorem lifecycleCut_tk {c : Cfg} {z : State} {t o : Nat} (hst : (z.tk t).st = .claimed) (ho : (z.tk t).owner = some o)
    (l : Option Nat) : (lifecycleCut c l z).tk t = z.tk t := by
  have hfin : finished c z o = false := by simp [finished, idleFree, holds_of hst ho]
  have hpl : (pool c z).contains t = false := by simp [pool, claimable, startable, hst]
  exact lifecycleCut_inv (fun y => y.tk t = z.tk t)
    (fun y b hy => by
      split
      · rename_i hh
        have hb : b ≠ o := by rintro rfl; simp [hfin] at hh
        rw [endAgent_tk, hy]; simp [held, ho, Ne.symm hb]
      · exact hy)
    (fun y b hy => by split; simp only [post_tk, setAg_tk]; exact hy; exact hy)
    (fun y u hy => by
      by_cases e : t = u
      · subst e; rw [spawnFor_not hpl]; exact hy
      · rw [spawnFor_tk_ne e]; exact hy) l rfl

/-- the sweep of a cut tick, and the same cut of the sweep with end_agent's removals left out (W2) -/
def cutSweep (c : Cfg) (k : Cut) (s : State) (ends : Bool) : Git :=
  let r := reapCut c k.reap s
  (cutL k.git c.wtIds).foldl (fun g w => if sweeps c r w || (ends && endRemoves c r w) then g.rm c w else g) r.git

theorem tickCut_git (c : Cfg) (k : Cut) (s : State) : (tickCut c k s).git = cutSweep c k s true := by
  simp [tickCut, cutSweep]

/-- N1, W1 and W2 of a tick cut anywhere: it keeps every agent that holds work once its reap has run, reap takes no claim
from a live owner whose job runs, GC removes only what is clean and on a protected ref, and ending an agent removes no
worktree and deletes no branch -/
def N1cut (c : Cfg) : Prop :=
  (∀ s k a, Reachable c s → holdsWork c (reapCut c k.reap s) a = true → keptBy s (tickCut c k s) a = true)
  ∧ (∀ s k t o, Reachable c s → (s.tk t).st = .claimed → (s.tk t).owner = some o → (s.agt o).live = true →
      (s.agt o).bg = true → ((tickCut c k s).tk t).owner = some o)
  ∧ (∀ s k, Reachable c s → gcOk c s (tickCut c k s).git = true)
  ∧ (∀ s k, Reachable c s → cutSweep c k s true = cutSweep c k s false)

/-- N1, W1 and W2 of a cut tick, with the switches `N1_of` takes -/
theorem N1cut_of (c : Cfg) (hrel : c.release = .idle) (hbk : c.bgKeeps = true) (haw : c.allWts = true)
    (hbl : c.bgLives = true) (hoa : c.ownAdded = true) (hp : c.perTaskBase = true) (hs : c.splitGC = true) : N1cut c := by
  refine ⟨fun s k a _ h => ?_, fun s k t o _ hst ho hl hbg => ?_, fun s k _ => ?_, fun s k _ => ?_⟩
  · have hz : (reapCut c k.reap s).agt a = s.agt a := agt_of_ag (reapCut_ag ..) a
    have hl : ((reapCut c k.reap s).agt a).live = true := by
      simp only [holdsWork, Bool.and_eq_true] at h; exact h.1
    have := lifecycleCut_keeps (finished_of_holds hbl haw hoa hp h) hl k.life
    simp only [keptBy, beq_iff_eq, tickCut_agt]
    rw [this, hz]
  · have hk : keeps c (s.agt o) = true := by simp [keeps, hrel, hbk, hl, hbg]
    have hr : ∀ l : List Nat, (l.foldl (reapTask c) s).tk t = s.tk t := fun l =>
      (foldl_inv (reapTask c) (fun y : State => y.tk t = s.tk t ∧ y.ag = s.ag) l s ⟨rfl, rfl⟩
        (fun y u hy => ⟨by rw [reapTask_keeps (by rw [hy.1]; exact ho) (by rw [agt_of_ag hy.2]; exact hk), hy.1],
          by rw [reapTask_ag]; exact hy.2⟩)).1
    have hz : (reapCut c k.reap s).tk t = s.tk t := by
      cases k.reap with
      | none => show (reapLocks (reapTasks c s)).tk t = _; rw [tk_of_task (reapLocks_task _)]; exact hr c.tasks
      | some n => show (reapLocksN _ _).tk t = _; rw [tk_of_task (reapLocksN_task ..)]; exact hr _
    rw [tickCut_tk, lifecycleCut_tk (by rw [hz]; exact hst) (by rw [hz]; exact ho), hz, ho]
  · rw [tickCut_git]
    exact gitFold_gcOk hs s _ (reapCut_git ..) (reapCut_ag ..) _
  · simp [cutSweep, endRemoves, hs]

/-- Q1 of a cut tick: whatever reap, the sweep and lifecycle got through, a tick whose notice pass ran whole leaves the
latest question of every blocked task told -/
theorem Q1cut {c : Cfg} (hr : c.renotify = true) (s : State) (k : Cut) (hn : k.note = none) {t : Nat} (ht : t ∈ c.tasks)
    (hb : ((tickCut c k s).tk t).st = .blocked) : toldAfter (tickCut c k s).evs t = true := by
  simp only [tickCut, hn, cutL] at hb ⊢
  rw [tk_of_task (notesL_task ..)] at hb
  exact (notices_tells hr c.tasks _).1 ht hb

-- ---------- what passGuard buys ----------

/-- a failed pass stops no other pass: whatever unit of whichever pass an error ends, the tick may still run each other
pass whole -/
def PassesIndep (c : Cfg) : Prop := ∀ v : Option Nat,
  Cut.ok c ⟨v, none, none, none⟩ ∧ Cut.ok c ⟨none, v, none, none⟩ ∧ Cut.ok c ⟨none, none, v, none⟩ ∧
    Cut.ok c ⟨none, none, none, v⟩

theorem passesIndep_of {c : Cfg} (hg : c.passGuard = true) : PassesIndep c :=
  fun _ => ⟨Or.inl hg, Or.inl hg, Or.inl hg, Or.inl hg⟩

/-- without the guard an error ends the tick: reap failing at its first unit runs no other pass -/
theorem seq_reap0 {c : Cfg} {n : Nat} (h : (Cut.seq c n).reap = some 0) : Cut.seq c n = ⟨some 0, some 0, some 0, some 0⟩ := by
  unfold Cut.seq at h ⊢; simp only [] at h ⊢
  split
  · rename_i hn; simp [hn] at h; subst h; rfl
  · split <;> (try split) <;> simp_all

theorem tickCut_none (c : Cfg) (s : State) : tickCut c ⟨some 0, some 0, some 0, some 0⟩ s = s := by
  have hl : reapLocksN 0 s = s := by
    simp only [reapLocksN]; congr 1
    apply List.ext_getElem?; intro i; rw [List.getElem?_mapIdx]; cases s.lock[i]? <;> simp
  simp [tickCut, reapCut, lifecycleCut, cutL, hl]

/-- finding #36: without `passGuard`, a tick whose reap fails at its first unit does nothing: if the error recurs (a row
reap chokes on), watchd never again tells a block, ends, digests, spawns or sweeps -/
theorem stuck36 {c : Cfg} (hg : c.passGuard = false) {k : Cut} (hk : k.ok c) (h0 : k.reap = some 0) (s : State) :
    tickCut c k s = s := by
  rcases hk with h | ⟨n, rfl⟩
  · rw [hg] at h; cases h
  · rw [seq_reap0 h0]; exact tickCut_none c s

theorem not_passesIndep {c : Cfg} (hg : c.passGuard = false) : ¬ PassesIndep c := by
  intro h
  rcases (h (some 0)).1 with e | ⟨n, hn⟩
  · rw [hg] at e; cases e
  · have := seq_reap0 (n := n) (c := c) (by rw [← hn])
    rw [← hn] at this; cases this

-- #36 as a run: agent 0 claims #1 and blocks on it; a tick whose reap fails at its first unit tells the communicator
-- nothing without the guard, and the block with it
def pre36 : List Action := [.add [], .claim 0 1, .block 0 1]
example : (run { passGuard := false } pre36).any (fun s =>
    ((tickCut { passGuard := false } (Cut.seq { passGuard := false } 0) s).tk 1).st == .blocked
      && !toldAfter (tickCut { passGuard := false } (Cut.seq { passGuard := false } 0) s).evs 1) = true := by decide +kernel
example : (run {} pre36).any (fun s => toldAfter (tickCut {} ⟨some 0, none, none, none⟩ s).evs 1) = true := by decide +kernel

/-- the instance the replay runs: N1, W1 and W2 of every cut tick, and no pass stops another -/
theorem replay_cut : N1cut replay ∧ PassesIndep replay :=
  ⟨N1cut_of _ rfl rfl rfl rfl rfl rfl rfl, passesIndep_of rfl⟩

end Swarm
