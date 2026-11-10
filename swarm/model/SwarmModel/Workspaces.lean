import SwarmModel.Fair

/-! sw-bases' theorems W1-W4 (board #2), and that each fails on the current Cfg: the runs of findings #18-#21 made into
refutations. W3 speaks of fair runs; its counterexamples are two-state loops (`loopOk`) made into fair `Run`s. The fix's
switches (`perTaskBase`, `splitGC`, `recordedWorkspaces`) are defined in Model.lean; that W1-W4 hold with them on is
board #6. -/

namespace Swarm
set_option linter.unusedSimpArgs false

/-- W1: GC removes a worktree only if it is clean, unattached, no process is inside and its HEAD is reachable from a
protected ref; it deletes a branch only if it is no protected ref and its tip is reachable from one -/
def W1 (c : Cfg) : Prop := ∀ s act s', Reachable c s → step c s act = some s' → gcOk c s s'.git = true
/-- W2: ending an agent removes no worktree and deletes no branch: a tick does to git only what the sweep does -/
def W2 (c : Cfg) : Prop := ∀ s, Reachable c s → endKeepsGit c s = true
/-- W3: on a fair run no worktree stays an orphan forever (it is removed), and no agent stays idle and free with its work on
a base forever (it is ended, or goes back to work) -/
def W3 (c : Cfg) : Prop := ∀ r : Run c, r.Fair → ∀ n,
  (∀ w, ∃ m ≥ n, orphan c (r.st m) w = false) ∧ ∀ a, ∃ m ≥ n, doneOnBase c (r.st m) a = false
/-- W4: no worktree has a base checked out -/
def W4 (c : Cfg) : Prop := ∀ s, Reachable c s → noBaseOut c s = true

/-- a run that ends in a state breaking `p` refutes `p` of every reachable state -/
theorem not_inv {c : Cfg} {acts : List Action} {p : State → Bool} (h : violates c acts p = true) :
    ¬ ∀ s, Reachable c s → p s = true := by
  intro hall
  unfold violates at h
  cases e : run c acts with
  | none => simp [e] at h
  | some s => simp [e] at h; simp [hall s (reachable_of_run e)] at h

theorem not_W1_of {c : Cfg} {acts : List Action} (h : w1Breaks c acts = true) : ¬ W1 c := by
  intro hw
  unfold w1Breaks at h
  cases e : run c acts with
  | none => simp [e] at h
  | some s =>
    simp only [e, Option.any_some, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    cases e2 : step c s .tick with
    | none => simp [e2] at h1
    | some s' =>
      have h3 := hw s .tick s' (reachable_of_run e) e2
      have : s' = tickOf c s := by
        simp only [step, tick, when] at e2; split at e2 <;> simp_all
      subst this; simp_all

/-- the two-state loop `s -x-> s' -y-> s` as a run -/
def loop2 (c : Cfg) (s s' : State) (x y : Action) (hx : step c s x = some s') (hy : step c s' y = some s) : Run c where
  st n := if n % 2 = 0 then s else s'
  act n := if n % 2 = 0 then x else y
  ok n := by
    by_cases h : n % 2 = 0
    · have : (n + 1) % 2 ≠ 0 := by omega
      simp [h, this, hx]
    · have : (n + 1) % 2 = 0 := by omega
      simp [h, this, hy]

/-- a loop `loopOk` accepts is a fair run on which `p` holds at every step -/
theorem forever_of_loopOk {c : Cfg} {pre : List Action} {x y : Action} {p : State → Bool}
    (h : loopOk c pre x y p = true) : ∃ r : Run c, r.Fair ∧ ∀ n, p (r.st n) = true := by
  unfold loopOk at h
  cases e : run c pre with
  | none => simp [e] at h
  | some s =>
    simp only [e, Option.any_some] at h
    cases ex : step c s x with
    | none => simp [ex] at h
    | some s' =>
      simp only [ex, Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨hy, hp⟩, hp'⟩, ho⟩, ho'⟩ := h
      refine ⟨loop2 c s s' x y ex hy, ?_, fun n => by simp only [loop2]; split <;> assumption⟩
      intro f hf N
      obtain ⟨n, -, hfn, hen⟩ := hf 0
      have hxy : f = x ∨ f = y := by
        have key : ∀ t, onlyFair c t [x, y] = true → f ∈ fair c t → (step c t f).isSome = true → f = x ∨ f = y := by
          intro t ht hm he
          simp only [onlyFair, List.all_eq_true] at ht
          have := ht f hm
          simp only [Bool.or_eq_true, Option.isNone_iff_eq_none, List.contains_cons, List.contains_nil,
            Bool.or_false, beq_iff_eq] at this
          rcases this with h0 | h0
          · simp [h0] at he
          · simpa using h0
        simp only [loop2] at hfn hen
        by_cases hn : n % 2 = 0
        · simp only [hn, if_true] at hfn hen; exact key s ho hfn hen
        · simp only [hn, if_false] at hfn hen; exact key s' ho' hfn hen
      rcases hxy with h | h
      · exact ⟨2 * N, by omega, by simp [loop2, h]⟩
      · exact ⟨2 * N + 1, by omega, by simp [loop2, h, show (2 * N + 1) % 2 ≠ 0 by omega]⟩

/-- a W3 counterexample: a fair run keeping worktree w an orphan forever -/
theorem not_W3_wt {c : Cfg} {pre : List Action} {x y : Action} {w : Nat}
    (h : loopOk c pre x y (orphan c · w) = true) : ¬ W3 c := by
  intro hw
  obtain ⟨r, hf, hp⟩ := forever_of_loopOk h
  obtain ⟨m, -, hm⟩ := (hw r hf 0).1 w
  simp [hp m] at hm

/-- a W3 counterexample: a fair run keeping agent a idle with its work on a base forever -/
theorem not_W3_agent {c : Cfg} {pre : List Action} {x y : Action} {a : Nat}
    (h : loopOk c pre x y (doneOnBase c · a) = true) : ¬ W3 c := by
  intro hw
  obtain ⟨r, hf, hp⟩ := forever_of_loopOk h
  obtain ⟨m, -, hm⟩ := (hw r hf 0).2 a
  simp [hp m] at hm

-- ---------- each fails on the current Cfg ----------
/-- #18: the sweep deletes `formal`, a base -/
theorem not_W1_branch : ¬ W1 cfg18 := not_W1_of (by decide : w1Breaks cfg18 pre18 = true)
/-- #18b: end_agent removes a worktree with a process inside -/
theorem not_W1_proc : ¬ W1 cfg18b := not_W1_of (by decide : w1Breaks cfg18b pre18b = true)
/-- #19: ending an agent removes its worktree (by design today) -/
theorem not_W2 : ¬ W2 cfg18b := not_inv (by decide : violates cfg18b pre19 (endKeepsGit cfg18b) = true)
/-- #20: work landed on `formal` keeps its worktree forever -/
theorem not_W3_formal_wt : ¬ W3 cfg20 :=
  not_W3_wt (by decide : loopOk cfg20 pre20 (.bgStart 1) (.bgEnd 1) (orphan cfg20 · 0) = true)
/-- #20: an agent whose task landed on `formal` is never ended -/
theorem not_W3_formal_agent : ¬ W3 cfg20b :=
  not_W3_agent (by decide : loopOk cfg20b pre20b (.bgStart 1) (.bgEnd 1) (doneOnBase cfg20b · 0) = true)
/-- #21: an agent checks out a base -/
theorem not_W4 : ¬ W4 cfg21 := not_inv (by decide : violates cfg21 pre21 (noBaseOut cfg21) = true)

end Swarm
