import SwarmModel.Taken

/-! sw-bases' theorems W1-W4 (board #2), each refuted with its fix's switch off (the runs of findings #18-#21) and proved
with it on (board #6): `W1_of`, `W2_of` (`splitGC`), `W3_of` (`perTaskBase`, `splitGC`, over fair runs), `W4_of`
(`recordedWorkspaces`). W3's counterexamples are two-state loops (`loopOk`) made into fair `Run`s. -/

namespace Swarm
set_option linter.unusedSimpArgs false

/-- W1: GC removes a worktree only if it is clean, unattached, no process is inside and its HEAD is reachable from a
protected ref; it deletes a branch only if it is no protected ref and its tip is reachable from one -/
def W1 (c : Cfg) : Prop := ∀ s act s', Reachable c s → step c s act = some s' → gcOk c s s'.git = true
/-- W2: ending an agent removes no worktree and deletes no branch: a tick does to git only what the sweep does -/
def W2 (c : Cfg) : Prop := ∀ s, Reachable c s → endKeepsGit c s = true
/-- W3: on a fair run no worktree stays an orphan forever (it is removed), and no agent stays idle and free with its work on
a base forever (it is ended, or goes back to work) -/
def W3 (c : Cfg) : Prop := ∀ r : Run c, r.Fair → ∀ n, Reachable c (r.st n) →
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

/-- a loop `loopOk` accepts is a fair run from a reachable state on which `p` holds at every step -/
theorem forever_of_loopOk {c : Cfg} {pre : List Action} {x y : Action} {p : State → Bool}
    (h : loopOk c pre x y p = true) : ∃ r : Run c, r.Fair ∧ Reachable c (r.st 0) ∧ ∀ n, p (r.st n) = true := by
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
      refine ⟨loop2 c s s' x y ex hy, ?_, by simpa [loop2] using reachable_of_run e,
        fun n => by simp only [loop2]; split <;> assumption⟩
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
  obtain ⟨r, hf, h0, hp⟩ := forever_of_loopOk h
  obtain ⟨m, -, hm⟩ := (hw r hf 0 h0).1 w
  simp [hp m] at hm

/-- a W3 counterexample: a fair run keeping agent a idle with its work on a base forever -/
theorem not_W3_agent {c : Cfg} {pre : List Action} {x y : Action} {a : Nat}
    (h : loopOk c pre x y (doneOnBase c · a) = true) : ¬ W3 c := by
  intro hw
  obtain ⟨r, hf, h0, hp⟩ := forever_of_loopOk h
  obtain ⟨m, -, hm⟩ := (hw r hf 0 h0).2 a
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
  obtain ⟨⟨⟨_, ⟨h1, _⟩, _⟩, _⟩, _⟩ := hend
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
    | (left; simp only [step, bgStart, bgEnd, bgStall, claim, claimRead, claimWrite, renew, release, block, done, dropOwn, lock, unlock, postTo,
        readAll, stop, wake, wakeRead, wakeWrite, prompt, boot, waiterGone, age, cool, expire, expireLock, leave, leaveIf,
        hcPrompt, hcClear, die, reapGone, add, after, unblock, drop, releaseOther, endOther, awayOn, back, commsRead, stale, nudge, hnudge, stay, endStay, stayCheck, stayHung, openPr, push, merge, finish, ciRun, poll, when] at h
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

theorem reapCut_git (c : Cfg) (o : Option Nat) (s : State) : (reapCut c o s).git = s.git := by
  cases o with
  | none => exact reapTasks_git c s
  | some n =>
    exact foldl_inv (reapTask c) (fun x : State => x.git = s.git) _ _ rfl (fun b a h => by
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

theorem tickCut_noBase {c : Cfg} {s : State} (h : NoBase c s.git) (k : Cut) : NoBase c (tickCut c k s).git := by
  simp only [tickCut, notesL_git, reapCut_git]
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
    | cut k _ _ _ ih => exact tickCut_noBase ih k
  intro s hr; exact noBase_of (this s hr)


-- ---------- W1 and W2 with `splitGC` on ----------

/-- no worktree went away and no branch was deleted -/
def Grows (g g' : Git) : Prop :=
  (∀ w, (g.wt w).on = true → (g'.wt w).on = true) ∧ ∀ b, (g.tip b).isSome = true → (g'.tip b).isSome = true

theorem grows_refl (g : Git) : Grows g g := ⟨fun _ h => h, fun _ h => h⟩
theorem grows_trans {g g' g'' : Git} (h1 : Grows g g') (h2 : Grows g' g'') : Grows g g'' :=
  ⟨fun w h => h2.1 w (h1.1 w h), fun b h => h2.2 b (h1.2 b h)⟩
theorem grows_setWt {g : Git} {w : Nat} {f : Wt → Wt} (hf : ∀ x, x.on = true → (f x).on = true) :
    Grows g (g.setWt w f) := by
  refine ⟨fun v hv => ?_, fun b hb => hb⟩
  rw [wt_setWt]; split
  · rename_i h; obtain ⟨rfl, _⟩ := h; exact hf _ hv
  · exact hv
theorem tip_setBr (g : Git) (b k v : Nat) : (g.setBr b k).tip v = if v = b ∧ b < g.brs.length then some k else g.tip v := by
  simp only [Git.setBr, Git.tip, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hv : v = b
  · subst hv; by_cases h : v < g.brs.length <;> simp [h]
  · simp [hv, Ne.symm hv]
theorem grows_setBr (g : Git) (b k : Nat) : Grows g (g.setBr b k) :=
  ⟨fun _ h => h, fun v hv => by rw [tip_setBr]; split <;> simp_all⟩
theorem grows_mkCommit (g : Git) (k : Nat) : Grows g (g.mkCommit k) := ⟨fun _ h => h, fun _ h => h⟩
theorem grows_mkSquash (g : Git) (k h : Nat) : Grows g (g.mkSquash k h) := ⟨fun _ h => h, fun _ h => h⟩

theorem gcOk_grows {c : Cfg} {s : State} {g' : Git} (h : Grows s.git g') : gcOk c s g' = true := by
  simp only [gcOk, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun w _ => ?_, fun b _ => ?_⟩
  · by_cases hon : (s.git.wt w).on = true
    · simp [hon, h.1 w hon]
    · simp [hon]
  · by_cases ht : (s.git.tip b).isSome = true
    · have := h.2 b ht
      simp only [ht, Bool.true_and, Bool.not_eq_true', Bool.or_eq_true]
      left; simpa [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] using this
    · simp [ht]

theorem grows_gitDo (c : Cfg) (s : State) (a : Nat) (op : GitOp) : Grows s.git (gitDo c s a op).2.1 := by
  cases op with
  | add w => exact grows_trans (grows_setWt (fun _ _ => rfl)) (grows_setBr ..)
  | edit w => exact grows_setWt (fun _ h => h)
  | commit w =>
    simp only [gitDo]
    have h := grows_trans (grows_mkCommit s.git (s.git.wt w).head)
      (grows_setWt (g := s.git.mkCommit (s.git.wt w).head) (w := w)
        (f := ({ · with head := s.git.next, dirty := false, recent := true })) (fun _ h => h))
    split
    · exact grows_trans h (grows_setBr ..)
    · exact h
  | land w b => exact grows_setBr ..
  | squash w b => exact grows_trans (grows_mkSquash ..) (grows_setBr ..)
  | checkout w b => exact grows_setWt (fun _ h => h)

theorem wt_rm (c : Cfg) (g : Git) (w v : Nat) :
    (g.rm c w).wt v = if v = w ∧ w < g.wts.length then { g.wt w with on := false } else g.wt v := by
  have e : (g.rm c w).wts = g.wts.set w { g.wt w with on := false } := by simp only [Git.rm]
  simp only [Git.wt, e, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hv : v = w
  · subst hv; by_cases hl : v < g.wts.length <;> simp [hl]
  · simp [hv, Ne.symm hv]
@[simp] theorem rm_cm (c : Cfg) (g : Git) (w : Nat) : (g.rm c w).cm = g.cm := rfl
@[simp] theorem rm_wts_length (c : Cfg) (g : Git) (w : Nat) : (g.rm c w).wts.length = g.wts.length := by simp [Git.rm]

/-- with `splitGC`, `git branch -D` only of a branch that is no base and is reachable from one -/
theorem tip_rm {c : Cfg} (hc : c.splitGC = true) (g : Git) (w v : Nat) :
    (g.rm c w).tip v = g.tip v ∨ ((g.rm c w).tip v = none ∧ c.nbases ≤ v ∧ g.safe c (g.tipOf v) = true) := by
  simp only [Git.rm, Git.tip]
  split
  · rename_i b _
    split
    · left; rfl
    · rename_i hcond
      simp only [hc, Bool.true_and, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', not_or,
        Bool.not_eq_false] at hcond
      by_cases hv : v = b
      · subst hv; right
        refine ⟨?_, by omega, hcond.2.2⟩
        simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
        by_cases hl : v < g.brs.length <;> simp [hl, List.getElem?_eq_none]
      · left; simp [List.getD_eq_getElem?_getD, List.getElem?_set, Ne.symm hv]
  · left; rfl

theorem safe_congr {c : Cfg} {g g0 : Git} (hcm : g.cm = g0.cm) (hb : ∀ b, b < c.nbases → g.tip b = g0.tip b) (k : Nat) :
    g.safe c k = g0.safe c k := by
  have : ∀ l : List Nat, (∀ b ∈ l, b < c.nbases) → l.any (g.reachFrom k) = l.any (g0.reachFrom k) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.any_cons]
      rw [ih (fun b hb => hl b (by simp [hb]))]
      simp only [Git.reachFrom, Git.cmt, hcm, hb x (hl x (by simp))]
  exact this _ (fun b hb => List.mem_range.1 hb)

theorem used_congr {c : Cfg} {s s' : State} (hag : s'.ag = s.ag) (hg : s'.git = s.git) (w : Nat) : used c s' w = used c s w := by
  have e : ∀ b, s'.agt b = s.agt b := fun b => agt_of_ag hag b
  simp only [used, wtmap, owns, e, hg]

@[simp] theorem reapLocks_git (s : State) : (reapLocks s).git = s.git := rfl

/-- what the sweep's fold keeps of git `g0`, deciding by state `r`: commits and bases as they were, a branch deleted only
if it is no base and was reachable from one, a worktree removed only if swept -/
def TickInv (c : Cfg) (r : State) (g0 g : Git) : Prop :=
  g.cm = g0.cm ∧ (∀ b, b < c.nbases → g.tip b = g0.tip b) ∧ (∀ b, g.tip b = g0.tip b ∨ g.tip b = none) ∧
    (∀ b, (g0.tip b).isSome = true → (g.tip b).isNone = true → c.nbases ≤ b ∧ g0.safe c (g0.tipOf b) = true) ∧
    (∀ w, (g0.wt w).on = true → (g.wt w).on = false → sweeps c r w = true)

/-- the tick's git, with `splitGC`: each worktree it removes was swept, each branch it deletes is no base and was
reachable from one -/
theorem gitFold_gcOk {c : Cfg} (hc : c.splitGC = true) (s r : State) (hrg : r.git = s.git) (hag : r.ag = s.ag)
    (l : List Nat) : gcOk c s (l.foldl (fun g w => if sweeps c r w || endRemoves c r w then g.rm c w else g) r.git) = true := by
  have hused : ∀ w, used c r w = used c s w := used_congr hag hrg
  have key : TickInv c r s.git (l.foldl (fun g w => if sweeps c r w || endRemoves c r w then g.rm c w else g) r.git) :=
    foldl_inv _ (TickInv c r s.git) l r.git
    (by
      rw [hrg]
      refine ⟨rfl, fun _ _ => rfl, fun _ => Or.inl rfl, fun b h1 h2 => ?_, fun w h1 h2 => ?_⟩
      · simp [Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] at h1 h2; exact absurd h2 h1
      · simp [h1] at h2)
    (by
      intro g w ⟨h1, h2, h3, h4, h5⟩
      simp only [endRemoves, hc, Bool.not_true, Bool.false_and, Bool.or_false]
      split
      · rename_i hsw
        refine ⟨by rw [rm_cm]; exact h1, fun b hb => ?_, fun b => ?_, fun b hb0 hbn => ?_, fun v hv hoff => ?_⟩
        · rcases tip_rm hc g w b with e | ⟨_, hle, _⟩
          · rw [e]; exact h2 b hb
          · omega
        · rcases tip_rm hc g w b with e | ⟨e, _⟩
          · rw [e]; exact h3 b
          · exact Or.inr e
        · rcases tip_rm hc g w b with e | ⟨_, hle, hsafe⟩
          · rw [e] at hbn; exact h4 b hb0 hbn
          · rcases h3 b with e3 | e3
            · refine ⟨hle, ?_⟩
              rw [safe_congr h1 h2] at hsafe
              simpa [Git.tipOf, e3] using hsafe
            · exact h4 b hb0 (by simp [e3])
        · rw [wt_rm] at hoff
          split at hoff
          · rename_i hh; obtain ⟨rfl, _⟩ := hh; exact hsw
          · exact h5 v hv hoff
      · exact ⟨h1, h2, h3, h4, h5⟩)
  generalize l.foldl (fun g w => if sweeps c r w || endRemoves c r w then g.rm c w else g) r.git = G at key ⊢
  obtain ⟨_, _, _, h4, h5⟩ := key
  simp only [gcOk, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun w _ => ?_, fun b _ => ?_⟩
  · by_cases hon : (s.git.wt w).on = true
    · cases hoff : (G.wt w).on
      · have hsw := h5 w hon hoff
        simp only [sweeps, hc, hrg, hused, ite_true, Bool.and_eq_true, Bool.not_eq_true'] at hsw
        simp [hsw]
      · simp
    · simp [hon]
  · by_cases ht : (s.git.tip b).isSome = true
    · cases hn : G.tip b with
      | none =>
        obtain ⟨hle, hsafe⟩ := h4 b ht (by simp [hn])
        simp [hle, hsafe]
      | some _ => simp
    · simp [ht]

theorem gitTick_gcOk {c : Cfg} (hc : c.splitGC = true) (s : State) :
    gcOk c s (gitTick c (reapLocks (reapTasks c s))) = true :=
  gitFold_gcOk hc s _ (by rw [reapLocks_git, reapTasks_git]) (by simp) c.wtIds

/-- W1 with `splitGC` on: GC removes only a clean, unattached worktree with no process inside and its HEAD on a protected
ref, and deletes only a branch that is no base and is reachable from one -/
theorem W1_of (c : Cfg) (hc : c.splitGC = true) : W1 c := by
  intro s act s' _ hs
  rcases git_step hs with e | ⟨a, op, rfl⟩ | ⟨w, op, rfl⟩ | rfl
  · exact gcOk_grows (by rw [e]; exact grows_refl _)
  · simp only [step, gitCmd, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨_, rfl⟩ := hs
    simp only [setAg_git]
    exact gcOk_grows (grows_gitDo c s a op)
  · simp only [step, world, when, Option.ite_none_right_eq_some, Option.some.injEq] at hs
    obtain ⟨_, rfl⟩ := hs
    exact gcOk_grows (grows_setWt (fun x h => by cases op <;> exact h))
  · obtain ⟨_, _, rfl⟩ := step_tick hs
    rw [tickOf_git]
    exact gitTick_gcOk hc s

/-- W2 with `splitGC` on: ending an agent removes no worktree and deletes no branch -/
theorem W2_of (c : Cfg) (hc : c.splitGC = true) : W2 c := by
  intro s _
  simp [endKeepsGit, gitTick, sweepGit, endRemoves, hc]

-- ---------- W3 over fair runs: the orphan half (`splitGC`) ----------

theorem on_lt {g : Git} {w : Nat} (h : (g.wt w).on = true) : w < g.wts.length := by
  refine Classical.byContradiction fun hl => ?_
  simp [Git.wt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hl)] at h
  exact absurd h (by decide)

/-- a fold of removals leaves w removed if it removes it, or it was removed before -/
theorem fold_rm_off (c : Cfg) (cond : Nat → Bool) (w : Nat) : ∀ (l : List Nat) (g : Git),
    ((w ∈ l ∧ cond w = true ∧ w < g.wts.length) ∨ (g.wt w).on = false) →
    ((l.foldl (fun g v => if cond v = true then g.rm c v else g) g).wt w).on = false
  | [], g, h => by simpa using h
  | v :: vs, g, h => by
    simp only [List.foldl_cons]
    apply fold_rm_off c cond w vs
    have hoff : (g.wt w).on = false → (((if cond v = true then g.rm c v else g)).wt w).on = false := by
      intro h0; split
      · rw [wt_rm]; split <;> simp_all
      · exact h0
    by_cases hv : w = v
    · subst hv
      rcases h with ⟨_, hc, hl⟩ | h
      · right; simp only [hc, ↓reduceIte, wt_rm]; simp [hl]
      · exact Or.inr (hoff h)
    · rcases h with ⟨hm, hc, hl⟩ | h
      · left; refine ⟨by simpa [hv] using hm, hc, by split <;> simp [hl]⟩
      · exact Or.inr (hoff h)

/-- with `splitGC`, the tick removes an orphan -/
theorem orphan_tick {c : Cfg} (hc : c.splitGC = true) {s : State} {w : Nat} (h : orphan c s w = true) :
    ((tickS c s).git.wt w).on = false := by
  have hrg : (reapLocks (reapTasks c s)).git = s.git := by rw [reapLocks_git, reapTasks_git]
  have hused : ∀ w, used c (reapLocks (reapTasks c s)) w = used c s w := used_congr (by simp) hrg
  show ((gitTick c (reapLocks (reapTasks c s))).wt w).on = false
  simp only [orphan, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hw, hon⟩, hd⟩, hsafe⟩, hu⟩, hp⟩, hrec⟩ := h
  refine fold_rm_off c (fun v => sweeps c (reapLocks (reapTasks c s)) v || endRemoves c (reapLocks (reapTasks c s)) v) w
    c.wtIds _ (Or.inl ⟨List.mem_range.2 hw, ?_, by rw [hrg]; exact on_lt hon⟩)
  simp [sweeps, hc, hrg, reapTasks_git, hused, hon, hd, hsafe, hu, hp, hrec]

/-- W3, the orphan half: on a fair run with `splitGC` and watchd running, no worktree stays an orphan forever -/
theorem orphan_ev {c : Cfg} (hc : c.splitGC = true) (hw : c.watchd = true) (r : Run c) (hf : r.Fair) (n w : Nat) :
    ∃ m ≥ n, orphan c (r.st m) w = false := by
  refine Classical.byContradiction fun hne => ?_
  have hD : ∀ m, n ≤ m → orphan c (r.st m) w = true := fun m hm => by
    cases hx : orphan c (r.st m) w
    · exact absurd ⟨m, hm, hx⟩ hne
    · rfl
  have hoff : ∀ k, n ≤ k → orphan c (tickOf c (r.st k)) w = false := fun k hk => by
    simp [orphan, orphan_tick hc (hD k hk)]
  obtain ⟨k, hk, hact⟩ := Run.fair_ev hf (f := .tick) (N0 := n) (fun _ _ => by simp [fair]) (fun k hk => by
    have hne : tickOf c (r.st k) ≠ r.st k := fun e => by
      have h2 := hoff k hk; rw [e, hD k hk] at h2; cases h2
    simp [step, tick, when, hw, hne])
  have hok := r.ok k
  rw [hact] at hok
  obtain ⟨_, _, e⟩ := step_tick hok
  have h2 := hD (k + 1) (by omega)
  rw [e, hoff k hk] at h2; cases h2

-- ---------- W3 over fair runs: the agent half (`perTaskBase`) ----------

theorem reapTask_cases (c : Cfg) (x : State) (t : Nat) : reapTask c x t = x ∨ ∃ o, (x.tk t).owner = some o ∧
    (x.tk t).st = .claimed ∧ reapTask c x t =
      post (setTask x t fun r => { r with st := .opn, owner := none, lease := false, reaped := some o })
        ⟨none, o, false, .released, t⟩ := by
  unfold reapTask; simp only []; split
  · rename_i o ho
    split
    · rename_i hcd
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcd
      exact Or.inr ⟨o, ho, hcd.1.1, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem holds_iff (s : State) (a : Nat) : holds s a = true ↔ ∃ t, held (s.tk t) a = true := by
  constructor
  · intro h
    simp only [holds, List.any_eq_true] at h
    obtain ⟨k, hk, hh⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hk
    exact ⟨i + 1, by simpa [State.tk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using hh⟩
  · rintro ⟨t, ht⟩
    have hst : (s.tk t).st ≠ .absent := by intro e; simp [held, e] at ht
    have h := tk_in_range hst
    simp only [holds, List.any_eq_true]
    refine ⟨s.task[t - 1], List.getElem_mem h.2, ?_⟩
    have e : s.tk t = s.task[t - 1] := by
      simp [State.tk, h.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h.2]
    rw [← e]; exact ht

/-- reap takes nothing from an agent that holds nothing: the tasks it owns keep their owner -/
theorem reapTasks_owner {c : Cfg} {s : State} {a : Nat} (hh : holds s a = false) :
    (∀ u, held ((reapTasks c s).tk u) a = false) ∧ ∀ u, ((reapTasks c s).tk u).owner = some a ↔ (s.tk u).owner = some a := by
  have h0 : ∀ u, held (s.tk u) a = false := fun u => by
    cases e : held (s.tk u) a
    · rfl
    · exact absurd ((holds_iff s a).2 ⟨u, e⟩) (by simp [hh])
  unfold reapTasks
  refine foldl_inv (reapTask c) (fun x : State => (∀ u, held (x.tk u) a = false) ∧
    ∀ u, (x.tk u).owner = some a ↔ (s.tk u).owner = some a) c.tasks s ⟨h0, fun _ => Iff.rfl⟩ ?_
  intro x t ⟨h1, h2⟩
  rcases reapTask_cases c x t with e | ⟨o, ho, hcl, e⟩
  · rw [e]; exact ⟨h1, h2⟩
  · rw [e]
    have hoa : o ≠ a := by
      rintro rfl
      have := h1 t
      simp [held, ho, hcl] at this
    refine ⟨fun u => ?_, fun u => ?_⟩
    · rw [post_tk]
      rcases tk_setTask_or x t u (fun r => { r with st := .opn, owner := none, lease := false, reaped := some o }) with e | ⟨_, e⟩
      · rw [e]; exact h1 u
      · rw [e]; simp [held]
    · rw [post_tk]
      rcases tk_setTask_or x t u (fun r => { r with st := .opn, owner := none, lease := false, reaped := some o }) with e | ⟨rfl, e⟩
      · rw [e]; exact h2 u
      · rw [e, ← h2 u, ho]; simp [hoa]

theorem lockHeld_reap {s : State} {a : Nat} (h : lockHeld s a = false) : lockHeld (reapLocks s) a = false := by
  cases e : lockHeld (reapLocks s) a
  · rfl
  · exfalso
    simp only [lockHeld, reapLocks, List.any_map, List.any_eq_true, Function.comp_def] at e
    obtain ⟨l, hl, hx⟩ := e
    have : lockHeld s a = true := by
      simp only [lockHeld, List.any_eq_true]
      refine ⟨l, hl, ?_⟩
      split at hx <;> simp_all
    simp [h] at this

theorem wtmap_congr {c : Cfg} {s s' : State} (hag : s'.ag = s.ag) (hg : s'.git = s.git) (a : Nat) :
    wtmap c s' a = wtmap c s a := by
  have e : ∀ b, s'.agt b = s.agt b := fun b => agt_of_ag hag b
  simp only [wtmap, owns, e, hg]

theorem abases_congr {c : Cfg} {s s' : State} {a : Nat} (h : ∀ u, (s'.tk u).owner = some a ↔ (s.tk u).owner = some a) :
    abases c s' a = abases c s a := by
  have : (c.tasks.filter fun t => (s'.tk t).owner == some a) = c.tasks.filter fun t => (s.tk t).owner == some a :=
    List.filter_congr (fun t _ => by rw [Bool.eq_iff_iff]; simp only [beq_iff_eq]; exact h t)
  simp only [abases, this]

/-- reap keeps a finished agent finished -/
theorem finished_reap {c : Cfg} {s : State} {a : Nat} (h : finished c s a = true) :
    finished c (reapLocks (reapTasks c s)) a = true := by
  have hh : holds s a = false := by cases e : holds s a <;> simp_all [finished, idleFree]
  have hl : lockHeld s a = false := by cases e : lockHeld s a <;> simp_all [finished, idleFree]
  obtain ⟨hz1, hz2⟩ := reapTasks_owner (c := c) hh
  have hag : (reapLocks (reapTasks c s)).ag = s.ag := by simp
  have hg : (reapLocks (reapTasks c s)).git = s.git := by rw [reapLocks_git, reapTasks_git]
  have hown : ∀ u, ((reapLocks (reapTasks c s)).tk u).owner = some a ↔ (s.tk u).owner = some a := fun u => by
    rw [tk_of_task (reapLocks_task _)]; exact hz2 u
  have e1 : holds (reapLocks (reapTasks c s)) a = holds s a := by
    rw [hh]
    cases e : holds (reapLocks (reapTasks c s)) a
    · rfl
    · obtain ⟨t, ht⟩ := (holds_iff _ a).1 e
      rw [tk_of_task (reapLocks_task _), hz1 t] at ht; cases ht
  have e2 : lockHeld (reapLocks (reapTasks c s)) a = lockHeld s a := by
    rw [hl]; exact lockHeld_reap (by simpa [lockHeld] using hl)
  have e3 : unlanded c (reapLocks (reapTasks c s)) a = unlanded c s a := by
    simp only [unlanded, wtmap_congr hag hg, abases_congr hown, owns, State.agt, hag, hg]
  have e4 : (reapLocks (reapTasks c s)).agt a = s.agt a := agt_of_ag hag a
  simp only [finished, idleFree, e1, e2, e3, e4]
  exact h

theorem done_idle {c : Cfg} {s : State} {a : Nat} (h : doneOnBase c s a = true) : idleFree s a = true := by
  simp only [doneOnBase, Bool.and_eq_true] at h; exact h.1.1.1.1

/-- with `perTaskBase`, an agent idle with its work on its bases is what lifecycle calls finished -/
theorem done_finished {c : Cfg} (hp : c.perTaskBase = true) {s : State} {a : Nat} (h : doneOnBase c s a = true) :
    finished c s a = true := by
  simp only [doneOnBase, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have e : ∀ refs w, landedC c s.git refs w = s.git.landedIn refs w := fun _ _ => by simp [landedC, hp]
  have ek : ∀ refs k, landedK c s.git refs k = refs.any (s.git.reachFrom k) := fun _ _ => by simp [landedK, hp]
  simp only [finished, unlanded, e, ek, h1, h2, h3, h4, h5, Bool.true_and, Bool.false_or, Bool.and_false, Bool.false_and, Bool.not_false]

theorem idle_of {s : State} {a : Nat} (h : idleFree s a = true) :
    (s.agt a).st = .idle ∧ (s.agt a).reading = 0 ∧ (s.agt a).snap = [] := by
  simp only [idleFree, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_iff] at h
  exact ⟨h.1.1.1.1.1.1, h.1.2, h.2⟩

theorem lt_of_idle {s : State} {a : Nat} (h : (s.agt a).st = .idle) : a < s.ag.length := by
  refine Classical.byContradiction fun hl => ?_
  rw [agt_of_ge (Nat.le_of_not_lt hl)] at h; exact absurd h (by decide)

theorem spawnFor_aged (c : Cfg) (pl : List Nat) (y : State) (t b : Nat) :
    (spawnFor c pl y t).agt b = y.agt b ∨ ((spawnFor c pl y t).agt b).aged = false := by
  unfold spawnFor; split
  · split
    · simp only [claimed_agt, agt_mk, agt_def, agt_setAg]
      split
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- the tick that ends a finished agent leaves it ended, or its slot to a new agent (not aged): not idle and free -/
theorem ends_tick {c : Cfg} {s : State} {a : Nat} (ha : a ∈ c.agents) (hl : a < s.ag.length)
    (hE : ends c (reapLocks (reapTasks c s)) a = true) : idleFree (tickOf c s) a = false := by
  generalize hz : reapLocks (reapTasks c s) = z at hE
  have hzl : a < z.ag.length := by rw [← hz]; simpa using hl
  have hre : reusable c z a = false := by cases e : reusable c z a <;> simp_all [ends]
  have hE' := hE
  simp only [ends, Bool.and_eq_true, Bool.not_eq_true'] at hE'
  have hend : ((endFold c z).agt a).st = .ended := by
    unfold endFold
    suffices ∀ (l : List Nat) (y : State), y.ag.length = z.ag.length → (a ∈ l ∨ (y.agt a).st = .ended) →
        ((l.foldl (fun x b => if finished c z b && !reusable c z b then endAgent x b else x) y).agt a).st = .ended from
      this _ _ rfl (Or.inl ha)
    intro l
    induction l with
    | nil => intro y _ hm; simpa using hm
    | cons b bs ih =>
      intro y hy hm
      simp only [List.foldl_cons]
      apply ih
      · split
        · simp [endAgent, hy]
        · exact hy
      · split
        · by_cases hb : b = a
          · right; rw [endAgent_agt]; simp [hb, hy, hzl]
          · rcases hm with h | h
            · left; simpa [Ne.symm hb] using h
            · right; rw [endAgent_agt]; simp [hb, h]
        · rename_i hc
          by_cases hb : b = a
          · subst hb; exfalso; simp [hE'.1, hE'.2] at hc
          · rcases hm with h | h
            · left; simpa [Ne.symm hb] using h
            · exact Or.inr h
  have hdig : ((c.agents.foldl (digStep c z) (endFold c z)).agt a).st = .ended :=
    foldl_inv (digStep c z) (fun y : State => (y.agt a).st = .ended) c.agents _ hend (fun y b hy => by
      by_cases hb : b = a
      · subst hb; simp only [digStep, hre, Bool.false_and, Bool.false_eq_true, ↓reduceIte]; exact hy
      · rw [digStep_agt_ne hb]; exact hy)
  have hQ : ∀ y : State, ((y.agt a).st = .ended ∨ (y.agt a).aged = false) → idleFree y a = false := fun y hy => by
    rcases hy with hy | hy <;> simp [idleFree, hy]
  rw [tickOf_git, hz]
  show idleFree (lifecycle c z) a = false
  apply hQ
  rw [lifecycle_eq]
  split
  · exact Or.inl hdig
  · exact foldl_inv (spawnFor c (pool c z)) (fun y : State => (y.agt a).st = .ended ∨ (y.agt a).aged = false) c.tasks _
      (Or.inl hdig) (fun y t hy => by
        rcases spawnFor_aged c (pool c z) y t a with e | e
        · rw [e]; exact hy
        · exact Or.inr e)

theorem reapGone_breaks {c : Cfg} {s s' : State} {a : Nat} (h : step c s (.reapGone a) = some s') : idleFree s' a = false := by
  simp only [step, reapGone, leaveIf, when_eq_some] at h
  obtain ⟨hg, rfl⟩ := h
  have hl : a < s.ag.length := by
    refine Classical.byContradiction fun hl => ?_
    have hd : (default : Agent).dead = false := rfl
    simp [agt_of_ge (Nat.le_of_not_lt hl), Agent.live, hd] at hg
  simp [idleFree, endAgent_agt, agt_setAg, hl]

theorem wake_breaks {c : Cfg} {s s' : State} {a : Nat} (h : step c s (.wake a) = some s') : idleFree s' a = false := by
  simp only [step, wake, when_eq_some, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨_, hi⟩, _⟩, _⟩, rfl⟩ := h
  have hl := lt_of_idle hi
  simp [idleFree, awake, agt_setAg, hl]

theorem wakeRead_breaks {c : Cfg} {s s' : State} {a : Nat} (h : step c s (.wakeRead a) = some s') : idleFree s' a = false := by
  simp only [step, wakeRead, when_eq_some, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨_, hi⟩, _⟩, _⟩, hwk⟩, rfl⟩ := h
  have hl := lt_of_idle hi
  have hu : unread s a ≠ [] := by
    intro e; simp [wakes, e] at hwk
  simp [idleFree, agt_setAg, hl, hu]

theorem ready_wakes {s : State} {a : Nat} (h : Ready s a) : (s.agt a).waiter = true ∧ wakes s a = true := by
  obtain ⟨_, h2, _, h4, h5⟩ := h
  refine ⟨h2, ?_⟩
  simp [wakes, h4, List.isEmpty_iff, h5]

/-- W3, the agent half: on a fair run with `perTaskBase`, PR #116 and #119, watchd running and `hc ls` answering for
every row, from a reachable state, no agent stays idle and free with its task's work on that task's base forever. The
tick ends it, or (reusable) tells it of the pool and its waiter wakes it; a dead terminal's row is reaped. -/
theorem agent_ev {c : Cfg} (hp : c.perTaskBase = true) (hw : c.watchd = true) (hpo : c.passedOver = true)
    (hwa : c.waiterAlive = true) (hh : c.hcSees = true) (hu : c.unbound = []) (r : Run c) (hf : r.Fair) {n : Nat}
    (hR : Reachable c (r.st n)) (a : Nat) : ∃ m ≥ n, doneOnBase c (r.st m) a = false := by
  refine Classical.byContradiction fun hne => ?_
  have hD : ∀ m, n ≤ m → doneOnBase c (r.st m) a = true := fun m hm => by
    cases hx : doneOnBase c (r.st m) a
    · exact absurd ⟨m, hm, hx⟩ hne
    · rfl
  have hRm : ∀ m, n ≤ m → Reachable c (r.st m) :=
    forever (fun m => Reachable c (r.st m)) n hR (fun k _ ih => .step _ ih (r.ok k))
  have hI : ∀ m, n ≤ m → idleFree (r.st m) a = true := fun m hm => done_idle (hD m hm)
  have haM : a ∈ c.agents := by
    have := lt_of_idle (idle_of (hI n (Nat.le_refl _))).1
    rw [(i1_of_reachable hR).1] at this
    simpa [Cfg.agents] using this
  let fW : Action := if c.racy then .wakeRead a else .wake a
  let E : Nat → Prop := fun m => ((r.st m).agt a).dead = true ∨ (((r.st m).agt a).waiter = true ∧ wakes (r.st m) a = true)
  -- reapGone or the waiter's wake, taken, ends a's idle stretch
  have hbreak : ∀ k, n ≤ k → r.act k = .reapGone a ∨ r.act k = fW → False := by
    intro k hk hact
    have hok := r.ok k
    have hd' := done_idle (hD (k + 1) (by omega))
    rcases hact with e | e <;> rw [e] at hok
    · rw [reapGone_breaks hok] at hd'; cases hd'
    · simp only [fW] at hok
      split at hok
      · rw [wakeRead_breaks hok] at hd'; cases hd'
      · rw [wake_breaks hok] at hd'; cases hd'
  -- E enables one of them
  have hen : ∀ m, n ≤ m → E m → (step c (r.st m) (.reapGone a)).isSome = true ∨
      (fW ∈ fair c (r.st m) ∧ (step c (r.st m) fW).isSome = true) := by
    intro m hm hE
    obtain ⟨hi, hrd, hsn⟩ := idle_of (hI m hm)
    by_cases hdead : ((r.st m).agt a).dead = true
    · left; simp [step, reapGone, leaveIf, when, hw, hh, hu, hdead, Agent.live, hi, hrd, hsn]
    · right
      rcases hE with h | ⟨hwt, hwk⟩
      · exact absurd h hdead
      · have hd : ((r.st m).agt a).dead = false := by simpa using hdead
        simp only [fW]
        split
        · rename_i hr
          exact ⟨by simp [fair, haM, hd], by simp [step, wakeRead, when, hr, hi, hwt, hsn, hwk]⟩
        · rename_i hr
          exact ⟨by simp [fair, haM, hd], by simp [step, wake, when, hr, hi, hwt, hwk]⟩
  -- the tick, at a state without E: enabled, and it ends a or makes E
  have htick : ∀ k, n ≤ k → ¬ E k → (step c (r.st k) .tick).isSome = true ∧ (r.act k = .tick → E (k + 1)) := by
    intro k hk hnE
    have hfin := finished_reap (c := c) (done_finished hp (hD k hk))
    have hcur : ∀ b, (r.st k).cur b ≤ (r.st k).log.length := fun b => ((inbInv_of_reachable (hRm k hk)).2.2 b).1
    have hcold := (i1_of_reachable (hRm k hk)).2.2
    have hl : a < (r.st k).ag.length := lt_of_idle (idle_of (hI k hk)).1
    have heff : idleFree (tickOf c (r.st k)) a = false ∨
        (((tickOf c (r.st k)).agt a).waiter = true ∧ wakes (tickOf c (r.st k)) a = true) := by
      cases hre : reusable c (reapLocks (reapTasks c (r.st k))) a
      · left; exact ends_tick haM hl (by simp [ends, hfin, hre])
      · right; exact ready_wakes (reusable_ready hpo hwa hcur hcold haM hre)
    have hne : tickOf c (r.st k) ≠ r.st k := by
      intro e; rw [e] at heff
      rcases heff with h | h
      · rw [hI k hk] at h; cases h
      · exact hnE (Or.inr h)
    refine ⟨by simp [step, tick, when, hw, hne], fun hact => ?_⟩
    have hok := r.ok k
    rw [hact] at hok
    obtain ⟨_, _, e⟩ := step_tick hok
    rcases heff with h | h
    · rw [← e, hI (k + 1) (by omega)] at h; cases h
    · exact Or.inr (by rw [e]; exact h)
  -- so E comes back forever
  have hinf : ∀ N, ∃ m, N ≤ m ∧ n ≤ m ∧ E m := by
    intro N
    refine Classical.byContradiction fun hno => ?_
    have hnE : ∀ m, max N n ≤ m → ¬ E m := fun m hm hE => hno ⟨m, by omega, by omega, hE⟩
    obtain ⟨k, hk, hact⟩ := Run.fair_ev hf (f := .tick) (N0 := max N n) (fun _ _ => by simp [fair])
      (fun k hk => (htick k (by omega) (hnE k hk)).1)
    exact hnE (k + 1) (by omega) ((htick k (by omega) (hnE k hk)).2 hact)
  -- and with it reapGone or the wake, which fairness takes
  by_cases hrg : ∀ N, ∃ m ≥ N, (step c (r.st m) (.reapGone a)).isSome = true
  · obtain ⟨k, hk, e⟩ := hf (.reapGone a) (fun N => by
      obtain ⟨m, hm, he⟩ := hrg N
      exact ⟨m, hm, by simp [fair, haM], he⟩) n
    exact hbreak k hk (Or.inl e)
  · have : ∃ N0, ∀ m, N0 ≤ m → (step c (r.st m) (.reapGone a)).isSome = false := by
      refine Classical.byContradiction fun hno => hrg fun N => ?_
      refine Classical.byContradiction fun hno2 => hno ⟨N, fun m hm => ?_⟩
      cases e : (step c (r.st m) (.reapGone a)).isSome
      · rfl
      · exact absurd ⟨m, hm, e⟩ hno2
    obtain ⟨N0, hN0⟩ := this
    obtain ⟨k, hk, e⟩ := hf fW (fun N => by
      obtain ⟨m, hm, hnm, hE⟩ := hinf (max N N0)
      rcases hen m hnm hE with h1 | h1
      · rw [hN0 m (by omega)] at h1; cases h1
      · exact ⟨m, by omega, h1⟩) n
    exact hbreak k hk (Or.inr e)

/-- W3 with `perTaskBase` and `splitGC` on (and PR #116, #119, watchd, `hc ls` seeing every row): on a fair run from a
reachable state no worktree stays an orphan and no agent stays idle with its task's work on its base forever -/
theorem W3_of (c : Cfg) (hp : c.perTaskBase = true) (hs : c.splitGC = true) (hw : c.watchd = true)
    (hpo : c.passedOver = true) (hwa : c.waiterAlive = true) (hh : c.hcSees = true) (hu : c.unbound = []) : W3 c :=
  fun r hf n hR => ⟨fun w => orphan_ev hs hw r hf n w, fun a => agent_ev hp hw hpo hwa hh hu r hf hR a⟩

/-- every sw-bases theorem holds of the instance the replay runs -/
theorem replay_W : W1 replay ∧ W2 replay ∧ W3 replay ∧ W4 replay ∧ B1 replay :=
  ⟨W1_of _ rfl, W2_of _ rfl, W3_of _ rfl rfl rfl rfl rfl rfl rfl, W4_of _ rfl, B1_of _ rfl⟩

-- each finding's instance with its fix's switch on (#18-#21, #B1)
example : W1 { cfg18 with splitGC := true } ∧ W1 { cfg18b with splitGC := true } := ⟨W1_of _ rfl, W1_of _ rfl⟩
example : W2 { cfg18b with splitGC := true } := W2_of _ rfl
example : W3 { cfg20 with perTaskBase := true, splitGC := true } ∧ W3 { cfg20b with perTaskBase := true, splitGC := true } :=
  ⟨W3_of _ rfl rfl rfl rfl rfl rfl rfl, W3_of _ rfl rfl rfl rfl rfl rfl rfl⟩
example : W4 { cfg21 with recordedWorkspaces := true } := W4_of _ rfl
example : B1 { cfgB1 with perTaskBase := true } := B1_of _ rfl

end Swarm
