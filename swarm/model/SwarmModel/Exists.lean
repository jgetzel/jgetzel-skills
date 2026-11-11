import SwarmModel.Workspaces
import SwarmModel.Taken

/-! Non-vacuity (board #12): a fair run exists, so the theorems over `Run.Fair` (L1, L2, L3's halves, W3) are not true
of nothing. `lasso_run`: a run that ends in a cycle, every fair action enabled at a state of the cycle being in the
cycle, is a fair `Run`. `fair_run_exists`: one on `replay` (the instance the replay runs, every shipped fix on), from
the start, meeting the side conditions L1-L3 take: every state reachable, no dead terminal, no background job, and no
`leave`, `die`, `waiterGone`, `reapGone` or `bgStart`. -/

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

theorem walk_spec {c : Cfg} {d : State} : ∀ (acts : List Action) (s : State) (ss : List State), walk c s acts = some ss →
    ss.length = acts.length + 1 ∧ ss.getD 0 d = s ∧
      ∀ i < acts.length, step c (ss.getD i d) (acts.getD i .tick) = some (ss.getD (i + 1) d)
  | [], s, ss, h => by simp [walk] at h; subst h; simp
  | x :: xs, s, ss, h => by
    simp only [walk, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨s', hx, ss', hw, rfl⟩ := h
    obtain ⟨hl, h0, hi⟩ := walk_spec xs s' ss' hw
    refine ⟨by simp [hl], by simp, fun i hi' => ?_⟩
    cases i with
    | zero => simp only [List.getD_cons_zero, List.getD_cons_succ]; rw [h0]; exact hx
    | succ i => simpa using hi i (by simp at hi'; omega)

theorem getD_lt {α : Type} {l : List α} {d : α} {i : Nat} (hi : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

theorem all_getD {α : Type} {l : List α} {q : α → Bool} {d : α} (h : l.all q = true) {i : Nat} (hi : i < l.length) :
    q (l.getD i d) = true := by
  rw [getD_lt hi]; exact List.all_eq_true.1 h _ (List.getElem_mem hi)

/-- `pre` from the start, then `cyc` back to where `pre` ended; `p` holds at every state, `q` of every action, and every
fair action enabled at a state of the cycle is in `cyc` -/
def lassoRun (c : Cfg) (p : State → Bool) (q : Action → Bool) (pre cyc : List Action) : Bool :=
  match walk c (init c) pre with
  | none => false
  | some ps =>
    match walk c (ps.getD pre.length default) cyc with
    | none => false
    | some cs => !cyc.isEmpty && cs.getD cyc.length default == ps.getD pre.length default && ps.all p &&
        (pre ++ cyc).all q && cs.all fun s => p s && onlyFair c s cyc

/-- a lasso `lassoRun` accepts is a fair run from the start, `p` at every state and `q` of every action -/
theorem lasso_run {c : Cfg} {p : State → Bool} {q : Action → Bool} {pre cyc : List Action}
    (h : lassoRun c p q pre cyc = true) :
    ∃ r : Run c, r.Fair ∧ r.st 0 = init c ∧ (∀ n, p (r.st n) = true) ∧ ∀ n, q (r.act n) = true := by
  unfold lassoRun at h
  split at h
  · simp at h
  rename_i ps ep
  split at h
  · simp at h
  rename_i cs ec
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
  obtain ⟨⟨⟨⟨hne, hlast⟩, hp⟩, hq⟩, hc⟩ := h
  obtain ⟨pl, p0, pstep⟩ := walk_spec (d := default) pre _ ps ep
  obtain ⟨cl, c0, cstep⟩ := walk_spec (d := default) cyc _ cs ec
  have hk : 0 < cyc.length := List.length_pos_iff.2 hne
  have hcs : ∀ m, cs.getD (m % cyc.length) default ∈ cs := fun m => by
    rw [getD_lt (by rw [cl]; exact Nat.lt_succ_of_lt (Nat.mod_lt _ hk))]; exact List.getElem_mem _
  -- the cycle's step: index `j` of the cycle steps to `j + 1`, and the end of the cycle is its start
  have cyc_ok : ∀ m, step c (cs.getD (m % cyc.length) default) (cyc.getD (m % cyc.length) .tick) =
      some (cs.getD ((m + 1) % cyc.length) default) := by
    intro m
    rw [cstep _ (Nat.mod_lt _ hk)]
    have hm := Nat.mod_lt m hk
    by_cases hj : m % cyc.length + 1 < cyc.length
    · rw [Nat.add_mod, Nat.mod_eq_of_lt (a := 1) (by omega), Nat.mod_eq_of_lt hj]
    · have e : m % cyc.length + 1 = cyc.length := by omega
      have e2 : (m + 1) % cyc.length = 0 := by
        rw [Nat.add_mod]; by_cases h1 : cyc.length = 1
        · rw [h1]; exact Nat.mod_one _
        · rw [Nat.mod_eq_of_lt (a := 1) (by omega), e, Nat.mod_self]
      rw [e, e2, hlast, c0]
  refine ⟨⟨fun n => if n < pre.length then ps.getD n default else cs.getD ((n - pre.length) % cyc.length) default,
    fun n => if n < pre.length then pre.getD n .tick else cyc.getD ((n - pre.length) % cyc.length) .tick, fun n => ?_⟩,
    ?_, ?_, fun n => ?_, fun n => ?_⟩
  · by_cases hn : n < pre.length
    · simp only [if_pos hn]; rw [pstep n hn]
      by_cases hn1 : n + 1 < pre.length
      · rw [if_pos hn1]
      · rw [if_neg hn1, show n + 1 - pre.length = 0 by omega, Nat.zero_mod, c0, show n + 1 = pre.length by omega]
    · simp only [if_neg hn, if_neg (show ¬ n + 1 < pre.length by omega), show n + 1 - pre.length = (n - pre.length) + 1 by omega]
      exact cyc_ok _
  · intro f hf N
    obtain ⟨n, hn, hfm, hen⟩ := hf pre.length
    dsimp only at hfm hen
    simp only [if_neg (show ¬ n < pre.length by omega)] at hfm hen
    have hj := List.all_eq_true.1 hc _ (hcs (n - pre.length))
    simp only [Bool.and_eq_true, onlyFair, List.all_eq_true] at hj
    have hm := hj.2 f hfm
    simp only [Bool.or_eq_true, Option.isNone_iff_eq_none] at hm
    rcases hm with hm | hm
    · rw [hm] at hen; simp at hen
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.contains_iff_mem.1 hm)
    refine ⟨pre.length + cyc.length * N + i, by have : N ≤ cyc.length * N := Nat.le_mul_of_pos_left N hk; omega, ?_⟩
    simp only [if_neg (show ¬ pre.length + cyc.length * N + i < pre.length by omega),
      show pre.length + cyc.length * N + i - pre.length = cyc.length * N + i by omega,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hi, getD_lt hi]
  · by_cases h0 : 0 < pre.length
    · simp only [if_pos h0, p0]
    · simp only [if_neg h0, Nat.zero_sub, Nat.zero_mod, c0, show pre.length = 0 by omega, p0]; simp
  · dsimp only; split
    · exact all_getD hp (by omega)
    · exact (Bool.and_eq_true _ _ ▸ List.all_eq_true.1 hc _ (hcs _)).1
  · dsimp only; split
    · rename_i hn; rw [getD_lt hn]; exact List.all_eq_true.1 hq _ (List.mem_append_left _ (List.getElem_mem _))
    · rw [getD_lt (Nat.mod_lt _ hk)]; exact List.all_eq_true.1 hq _ (List.mem_append_right _ (List.getElem_mem _))

-- ---------- one on the replay instance ----------
/-- no agent's terminal is gone and none runs a background job -/
def calm (s : State) : Bool := s.ag.all fun g => !g.dead && !g.bg
/-- none of the actions L1-L3 rule out after their start -/
def quiet : Action → Bool
  | .leave _ | .die _ | .waiterGone _ | .reapGone _ | .bgStart _ => false
  | _ => true

/-- Task #1 is added; then agents 0 and 1 take turns: each claims it, its lease lapses, it releases it. Every fair action
enabled on the way (both claims, the expiry) is in the cycle, and the cycle ends where it began. -/
def preNV : List Action := [.add []]
def cycNV : List Action := [.claim 0 1, .expire 1, .release 0 1, .claim 1 1, .expire 1, .release 1 1]
theorem replay_lasso : lassoRun replay calm quiet preNV cycNV = true := by decide +kernel
-- the check bites: with agent 0 alone taking turns, agent 1's claim is enabled at every open state and never taken
example : lassoRun replay calm quiet preNV [.claim 0 1, .expire 1, .release 0 1] = false := by decide +kernel

/-- Non-vacuity: a fair run of `replay` from the start that meets the side conditions of L1-L3 (`startable_leads_to`,
`idleClaim_leads_to`, `holder_leads_to`) at every step. -/
theorem fair_run_exists : ∃ r : Run replay, r.Fair ∧ r.st 0 = init replay ∧ (∀ n, Reachable replay (r.st n)) ∧
    (∀ n b, ((r.st n).agt b).dead = false ∧ ((r.st n).agt b).bg = false) ∧
    ∀ n b, r.act n ≠ .leave b ∧ r.act n ≠ .die b ∧ r.act n ≠ .waiterGone b ∧ r.act n ≠ .reapGone b ∧ r.act n ≠ .bgStart b := by
  obtain ⟨r, hf, h0, hp, hq⟩ := lasso_run replay_lasso
  refine ⟨r, hf, h0, fun n => forever (fun m => Reachable replay (r.st m)) 0 (h0 ▸ .init) (fun k _ ih => .step _ ih (r.ok k)) n
    (Nat.zero_le n), ?_, ?_⟩
  · intro n b
    by_cases hb : b < (r.st n).ag.length
    · have := all_getD (d := default) (hp n) hb
      simp only [calm, Bool.and_eq_true, Bool.not_eq_true'] at this
      simpa [State.agt] using this
    · rw [agt_of_ge (by omega)]; exact ⟨rfl, rfl⟩
  · intro n b
    have := hq n
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro e; rw [e] at this; simp [quiet] at this)

/-- L1 applies to it: the theorem's hypotheses are met, not assumed. -/
example (t : Nat) (ht : t ∈ replay.tasks) : ∃ r : Run replay, r.Fair ∧
    ∃ m, ¬ (startable (r.st m) t = true ∧ slotFree replay (r.st m) = true) := by
  obtain ⟨r, hf, -, hR, hc, hq⟩ := fair_run_exists
  exact ⟨r, hf, (startable_leads_to (by decide) (by decide) (by decide) (by decide) (by decide) ht r hf (n := 0) (hR 0)
    (fun b => (hc 0 b).1) (fun k _ b => ⟨(hq k b).1, (hq k b).2.1, (hq k b).2.2.1, (hq k b).2.2.2.1⟩)).imp fun m h => h.2⟩

end Swarm
