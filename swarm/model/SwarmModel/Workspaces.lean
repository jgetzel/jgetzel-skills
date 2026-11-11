import SwarmModel.Fair

/-! sw-bases' theorems W1-W4 (board #2), and that each fails on the current Cfg: the runs of findings #18-#21 made into
refutations. W3 speaks of fair runs; its counterexamples are two-state loops (`loopOk`) made into fair `Run`s. The fix's
switches (`perTaskBase`, `splitGC`, `recordedWorkspaces`) are defined in Model.lean; that W4 holds with `recordedWorkspaces` on is `W4_of` (board #5); W1-W3 with the rest is board #6. -/

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

/-- B1: lifecycle ends an agent only if the worktree it works in is landed on a base of one of its tasks (main if none) -/
def B1 (c : Cfg) : Prop := ∀ s, Reachable c s → ∀ a w, ends c s a = true → wtmap c s a = some w →
  s.git.landedIn (abases c s a) w = true

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
/-- #B1: an agent whose work is on main, not on its task's base `formal`, is ended -/
theorem not_B1 : ¬ B1 cfgB1 := by
  intro h
  have key : (run cfgB1 preB1).any (fun s => ends cfgB1 s 0 && wtmap cfgB1 s 0 == some 0
      && !s.git.landedIn (abases cfgB1 s 0) 0) = true := by decide +kernel
  cases e : run cfgB1 preB1 with
  | none => simp [e] at key
  | some s =>
    simp only [e, Option.any_some, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at key
    obtain ⟨⟨h1, h2⟩, h3⟩ := key
    simp [h s (reachable_of_run e) 0 0 h1 h2] at h3

/-- with `perTaskBase` on, B1 holds: lifecycle's `unlanded` asks `abases` -/
theorem B1_of (c : Cfg) (hc : c.perTaskBase = true) : B1 c := by
  intro s _ a w hend hw
  simp only [ends, finished, unlanded, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at hend
  obtain ⟨⟨_, h1, _⟩, _⟩ := hend
  simp only [hw, Option.any_some, Bool.not_eq_false'] at h1
  simpa [landedC, hc] using h1

/-- #21: an agent checks out a base -/
theorem not_W4 : ¬ W4 cfg21 := not_inv (by decide : violates cfg21 pre21 (noBaseOut cfg21) = true)

-- ---------- W4 with `recordedWorkspaces` on ----------
set_option maxHeartbeats 1000000
@[simp] theorem setTask_git (s : State) (t : Nat) (f : Task → Task) : (setTask s t f).git = s.git := by frame setTask
@[simp] theorem setAg_git (s : State) (a : Nat) (f : Agent → Agent) : (setAg s a f).git = s.git := by frame setAg
@[simp] theorem post_git (s : State) (m : Msg) : (post s m).git = s.git := by frame post
@[simp] theorem showMsg_git (s : State) (a i : Nat) : (showMsg s a i).git = s.git := by frame showMsg
@[simp] theorem showAll_git (s : State) (a : Nat) (ids : List Nat) : (showAll s a ids).git = s.git := by
  induction ids generalizing s with
  | nil => rfl
  | cons i is ih => simp [showAll, List.foldl_cons] at ih ⊢; rw [ih]; simp
@[simp] theorem deliver_git (s : State) (a : Nat) : (deliver s a).git = s.git := by simp [deliver]
@[simp] theorem claimed_git (s : State) (a t : Nat) : (claimed s a t).git = s.git := by frame claimed
@[simp] theorem takes_git (c : Cfg) (s : State) (a t : Nat) : (takes c s a t).git = s.git := by frame takes
@[simp] theorem awake_git (s : State) (a : Nat) : (awake s a).git = s.git := by frame awake
@[simp] theorem unbelieve_git (s : State) (a t : Nat) : (unbelieve s a t).git = s.git := by frame unbelieve
@[simp] theorem endAgent_git (s : State) (a : Nat) : (endAgent s a).git = s.git := by frame endAgent

theorem git_step {c : Cfg} {s s' : State} {act : Action} (h : step c s act = some s') :
    s'.git = s.git ∨ (∃ a op, act = .git a op) ∨ (∃ w op, act = .world w op) ∨ act = .tick := by
  cases act <;> first
    | (right; left; exact ⟨_, _, rfl⟩) | (right; right; left; exact ⟨_, _, rfl⟩) | (right; right; right; rfl)
    | (left; simp only [step, bgStart, bgEnd, claim, claimRead, claimWrite, renew, release, block, done, dropOwn, lock, unlock, postTo,
        readAll, stop, wake, wakeRead, wakeWrite, prompt, boot, waiterGone, age, cool, expire, expireLock, leave, leaveIf,
        hcPrompt, hcClear, die, reapGone, add, after, unblock, drop, stale, nudge, when] at h
       (repeat' split at h) <;> first | (simp only [Option.some.injEq] at h; subst h; simp; done) | simp at h)

/-- no worktree that is there has a base checked out, per worktree -/
def NoBase (c : Cfg) (g : Git) : Prop := ∀ w, (g.wt w).on = true → ∀ b, (g.wt w).br = some b → c.nbases ≤ b

theorem wt_setWt (g : Git) (w v : Nat) (f : Wt → Wt) :
    (g.setWt w f).wt v = if v = w ∧ w < g.wts.length then f (g.wt w) else g.wt v := by
  simp only [Git.setWt, Git.wt, List.getD_eq_getElem?_getD, List.getElem?_modify]
  by_cases hv : v = w
  · subst hv; by_cases h : v < g.wts.length <;> simp [h]
  · simp [hv, Ne.symm hv]

theorem wt_setBr (g : Git) (b k v : Nat) : (g.setBr b k).wt v = g.wt v := rfl

@[simp] theorem setBr_wts (g : Git) (b k : Nat) : (g.setBr b k).wts = g.wts := rfl
@[simp] theorem mkCommit_wts (g : Git) (k : Nat) : (g.mkCommit k).wts = g.wts := rfl
@[simp] theorem mkSquash_wts (g : Git) (k h : Nat) : (g.mkSquash k h).wts = g.wts := rfl
theorem wt_mkCommit (g : Git) (k v : Nat) : (g.mkCommit k).wt v = g.wt v := rfl
theorem wt_mkSquash (g : Git) (k h v : Nat) : (g.mkSquash k h).wt v = g.wt v := rfl

theorem noBase_git {c : Cfg} (hc : c.recordedWorkspaces = true) {s s' : State} {a : Nat} {op : GitOp}
    (h : NoBase c s.git) (hs : gitCmd c s a op = some s') : NoBase c s'.git := by
  simp only [gitCmd, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
  obtain ⟨hg, rfl⟩ := hs
  simp only [setAg_git]
  unfold NoBase
  intro v hv b hb
  cases op with
  | add w =>
    simp only [gitDo, wt_setBr, wt_setWt] at hv hb
    by_cases hp : v = w ∧ w < s.git.wts.length
    · simp only [hp, and_self, ite_true] at hv hb; simp_all [Cfg.wbr]; omega
    · simp only [hp, ite_false] at hv hb; exact h v hv b hb
  | edit w =>
    simp only [gitDo, wt_setWt] at hv hb
    by_cases hp : v = w ∧ w < s.git.wts.length
    · simp only [hp, and_self, ite_true] at hv hb; exact h w hv b hb
    · simp only [hp, ite_false] at hv hb; exact h v hv b hb
  | commit w =>
    simp only [gitDo] at hv hb
    rcases hx : (s.git.wt w).br with _ | b0 <;> simp only [hx, wt_setBr, wt_mkCommit, wt_setWt, mkCommit_wts] at hv hb <;>
    (by_cases hp : v = w ∧ w < s.git.wts.length
     · simp only [hp, and_self, ite_true] at hv hb; exact h w hv b (by rw [hx]; exact hb)
     · simp only [hp, ite_false] at hv hb; exact h v hv b hb)
  | land w b' =>
    simp only [gitDo, wt_setBr] at hv hb; exact h v hv b hb
  | squash w b' =>
    simp only [gitDo, wt_setBr, wt_mkSquash] at hv hb; exact h v hv b hb
  | checkout w b' =>
    simp only [gitDo, wt_setWt] at hv hb
    by_cases hp : v = w ∧ w < s.git.wts.length
    · simp only [hp, and_self, ite_true] at hv hb
      simp only [Option.some.injEq] at hb
      subst hb
      simp [gitDo, hc, Cfg.wbr] at hg
      omega
    · simp only [hp, ite_false] at hv hb; exact h v hv b hb

theorem noBase_of {c : Cfg} {s : State} (h : NoBase c s.git) : noBaseOut c s = true := by
  simp only [noBaseOut, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff]
  intro w _
  by_cases hon : (s.git.wt w).on = true
  · right
    cases hb : (s.git.wt w).br with
    | none => rfl
    | some b => simpa using h w hon b hb
  · left; simpa using hon

theorem reapTasks_git (c : Cfg) (s : State) : (reapTasks c s).git = s.git :=
  foldl_inv (reapTask c) (fun x : State => x.git = s.git) _ _ rfl (fun b a h => by
    simp only [reapTask]; (repeat' split) <;> simp_all)

theorem rm_wt (c : Cfg) (g : Git) (w v : Nat) : ((g.rm c w).wt v).on = true → (g.rm c w).wt v = g.wt v := by
  intro h
  have e : (g.rm c w).wts = g.wts.set w { g.wt w with on := false } := by simp only [Git.rm]
  simp only [Git.wt, e, List.getD_eq_getElem?_getD, List.getElem?_set] at h ⊢
  by_cases hv : w = v
  · subst hv; by_cases hl : w < g.wts.length <;> simp [hl] at h ⊢
  · simp [hv]

theorem noBase_rm {c : Cfg} {g : Git} (w : Nat) (h : NoBase c g) : NoBase c (g.rm c w) := by
  intro v hv b hb
  have := rm_wt c g w v hv
  rw [this] at hv hb; exact h v hv b hb

theorem tick_git {c : Cfg} {s : State} (h : NoBase c s.git) : NoBase c (tickOf c s).git := by
  rw [tickOf_git]
  simp only [gitTick]
  rw [show (reapLocks (reapTasks c s)).git = s.git from reapTasks_git c s]
  exact foldl_inv _ (NoBase c) _ _ h (fun g w hg => by split; exact noBase_rm w hg; exact hg)

theorem noBase_step {c : Cfg} (hc : c.recordedWorkspaces = true) {s s' : State} {act : Action}
    (h : NoBase c s.git) (hs : step c s act = some s') : NoBase c s'.git := by
  rcases git_step hs with e | ⟨a, op, rfl⟩ | ⟨w, op, rfl⟩ | rfl
  · rw [e]; exact h
  · exact noBase_git hc h hs
  · simp only [step, world, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨hw, rfl⟩ := hs
    intro v hv b hb
    simp only [world, wt_setWt] at hv hb
    by_cases hp : v = w ∧ w < s.git.wts.length
    · simp only [hp, and_self, ite_true] at hv hb
      cases op <;> simp only [WOp.f] at hv hb <;> exact h w hv b hb
    · simp only [hp, ite_false] at hv hb; exact h v hv b hb
  · simp only [step, tick, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨_, rfl⟩ := hs
    exact tick_git h

/-- W4 with `recordedWorkspaces` on: no agent can put a base in a worktree, so none is ever refused `git push . HEAD:<base>` -/
theorem W4_of (c : Cfg) (hc : c.recordedWorkspaces = true) : W4 c := by
  have : ∀ s, Reachable c s → NoBase c s.git := by
    intro s hr
    induction hr with
    | init =>
      intro w hw
      have : ((init c).git.wt w).on = false := by
        simp only [init, Git.wt, List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
      simp [this] at hw
    | step act _ hs ih => exact noBase_step hc ih hs
  intro s hr; exact noBase_of (this s hr)


end Swarm
