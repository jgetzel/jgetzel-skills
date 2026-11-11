import SwarmModel.Taken

/-! L4 over fair runs: a row whose terminal is gone is eventually ended (`endAgent`: its claims and locks released). -/

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- With `racy = false` no agent is between a claim's read and write, or a waiter's read and write. -/
def Rz (s : State) : Prop := ∀ b, (s.agt b).reading = 0 ∧ (s.agt b).snap = []

theorem rz_frame {s s' : State} (hag : s'.ag = s.ag) (h : Rz s) : Rz s' := fun b => by rw [agt_of_ag hag]; exact h b

theorem rz_setAg {s : State} {a : Nat} {f : Agent → Agent}
    (hf : (s.agt a).reading = 0 ∧ (s.agt a).snap = [] → (f (s.agt a)).reading = 0 ∧ (f (s.agt a)).snap = []) (h : Rz s) :
    Rz (setAg s a f) := by
  intro b
  rw [agt_setAg]
  split
  · rename_i hab; obtain ⟨rfl, _⟩ := hab; exact hf (h _)
  · exact h b

theorem rz_showAll {s : State} {a : Nat} {ids : List Nat} (h : Rz s) : Rz (showAll s a ids) := fun b => by
  obtain ⟨bl, e⟩ := showAll_agt a ids b s
  rw [e]; exact h b
theorem rz_deliver {s : State} {a : Nat} (h : Rz s) : Rz (deliver s a) := rz_showAll h
theorem rz_takes {c : Cfg} {s : State} {a t : Nat} (h : Rz s) : Rz (takes c s a t) := fun b => by
  obtain ⟨bl, e⟩ := takes_agt c s a t b
  rw [e]; exact h b
theorem rz_setTask {s : State} {t : Nat} {f : Task → Task} (h : Rz s) : Rz (setTask s t f) := rz_frame (by simp) h
theorem rz_post {s : State} {m : Msg} (h : Rz s) : Rz (post s m) := rz_frame (by simp) h

theorem rz_endAgent {s : State} {a : Nat} (h : Rz s) : Rz (endAgent s a) := fun b => by
  rw [endAgent_agt]; split
  · simp; exact h b
  · exact h b

theorem rz_spawnFor {c : Cfg} {pl : List Nat} {x : State} {t : Nat} (h : Rz x) : Rz (spawnFor c pl x t) := by
  unfold spawnFor; split
  · split
    · intro b
      simp only [claimed_agt, agt_mk, agt_def, agt_setAg]
      split
      · exact ⟨rfl, rfl⟩
      · exact h b
    · exact h
  · exact h

theorem rz_tickOf {c : Cfg} {s : State} (h : Rz s) : Rz (tickOf c s) :=
  tick_inv Rz (fun x t hx => rz_frame (by simp) hx) (fun x hx => rz_frame (by simp) hx)
    (fun _ _ => rz_endAgent) (fun x a pl hx => rz_post (rz_setAg (fun hh => by simpa using hh) hx))
    (fun _ _ _ hx _ => rz_spawnFor hx) h

macro "rz_tac" : tactic => `(tactic|
  repeat (first
    | with_reducible assumption
    | (with_reducible apply rz_deliver)
    | (with_reducible apply rz_takes)
    | (with_reducible apply rz_setTask)
    | (with_reducible apply rz_post)
    | (with_reducible apply rz_showAll)
    | (refine rz_setAg ?_ ?_ <;> first | (intro hh; simp_all; done) | skip)
    | (refine rz_frame ?_ ‹Rz _› <;> rfl)))

theorem rz_step {c : Cfg} {s s' : State} {act : Action} (hr : c.racy = false) (hI : Rz s) (hs : step c s act = some s') :
    Rz s' := by
  open_step hs
  case tick => obtain ⟨_, rfl⟩ := hs; exact rz_tickOf hI
  case unblock t₀ =>
    split at hs
    · rw [when_eq_some] at hs; obtain ⟨_, rfl⟩ := hs; exact rz_frame (s := s) (by simp) hI
    · cases hs
  case leave a => obtain ⟨_, rfl⟩ := hs; exact rz_endAgent (rz_setAg (fun hh => by simpa using hh) hI)
  case reapGone a => obtain ⟨_, rfl⟩ := hs; exact rz_endAgent (rz_setAg (fun hh => by simpa using hh) hI)
  case claimRead => simp [hr] at hs
  case claimWrite => simp [hr] at hs
  case wakeRead => simp [hr] at hs
  case wakeWrite => simp [hr] at hs
  all_goals (obtain ⟨hg, rfl⟩ := hs)
  all_goals (try split)
  all_goals (try simp only [unbelieve, awake, claimed])
  all_goals rz_tac

theorem rz_of_reachable {c : Cfg} (hr : c.racy = false) {s : State} (h : Reachable c s) : Rz s :=
  reachable_induct (fun b => by simp only [init, State.agt, List.getD_eq_getElem?_getD, List.getElem?_map]; cases c.agents[b]? <;> exact ⟨rfl, rfl⟩) (fun _ _ _ _ hI hs => rz_step hr hI hs) h

/-- L4. In a fair run of an instance with watchd running (`watchd`), `hc ls` answering (`hcSees`) and `racy = false`,
from a reachable state, a row that is live with its terminal gone and an hc address (not `unbound`) doesn't stay so:
watchd's reap ends it (`endAgent`: its claims reopened, its locks freed), or something else ends it first. No action is
excluded from the run. Each of `watchd`, `hcSees` and the address is needed (findings #14, #15). -/
theorem deadLive_leads_to {c : Cfg} (hr : c.racy = false) (hw : c.watchd = true) (hh : c.hcSees = true) {a : Nat}
    (ha : a ∈ c.agents) (hb : c.unbound.contains a = false) (r : Run c) (hf : r.Fair) {n : Nat}
    (hR : Reachable c (r.st n)) (h : deadLive (r.st n) a = true) : ∃ m, n ≤ m ∧ deadLive (r.st m) a = false := by
  refine Classical.byContradiction fun hne => ?_
  have hD : ∀ m, n ≤ m → deadLive (r.st m) a = true := fun m hm => by
    cases hx : deadLive (r.st m) a
    · exact absurd ⟨m, hm, hx⟩ hne
    · rfl
  have hZ : ∀ m, n ≤ m → Rz (r.st m) :=
    forever (fun m => Rz (r.st m)) n (rz_of_reachable hr hR) (fun k hk ih => rz_step hr ih (r.ok k))
  have hb' : a ∉ c.unbound := by simpa using hb
  obtain ⟨k, hk, hact⟩ := Run.fair_ev hf (f := .reapGone a) (N0 := n) (fun k hk => by simp [fair, ha]) (fun k hk => by
    have hd := hD k hk
    simp [deadLive] at hd
    simp [step, reapGone, leaveIf, when, hw, hh, hb', hd, (hZ k hk a).1, (hZ k hk a).2])
  have hok := r.ok k
  rw [hact] at hok
  simp only [step, reapGone, leaveIf, when_eq_some] at hok
  obtain ⟨_, he⟩ := hok
  have hl : a < (r.st k).ag.length := by
    refine Classical.byContradiction fun hl => ?_
    have := hD k hk
    rw [deadLive, agt_of_ge (Nat.le_of_not_lt hl)] at this; exact absurd this (by decide)
  have := hD (k+1) (by omega)
  rw [← he] at this
  simp [deadLive, endAgent_agt, Agent.live, hl] at this

end Swarm
