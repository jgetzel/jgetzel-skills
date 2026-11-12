import SwarmModel.Workspaces
import SwarmModel.Boot

/-! N1 (board #15): no work lost. watchd's tick never ends an agent that holds work (a background job running, or a
worktree with work not on its task's base), reap never takes a claim from an owner whose job runs, an agent may claim
back what reap took from it, and workspace GC removes nothing that is not on a protected ref (W1). Refuted with each
fix's switch off (findings #10, #11, #12, #26, #27) and proved with them on: `N1_of`. -/

namespace Swarm
set_option linter.unusedSimpArgs false

/-- a holds work: it is live, and its background job runs, or a worktree it works in (wt_map) or owns is dirty or has its
HEAD on no base of a task it owns (main if none). Read off the state alone, whatever lifecycle's switches are -/
def holdsWork (c : Cfg) (s : State) (a : Nat) : Bool :=
  (s.agt a).live && ((s.agt a).bg || (wtmap c s a).any (!s.git.landedIn (abases c s a) ·)
    || (s.agt a).own.any fun (w, _) => owns s a w && !s.git.landedIn (abases c s a) w)

/-- s' leaves agent a as s had it, but for the pool ids a digest told it of: the same agent, not ended, its job, agent.wt
and worktrees its own still -/
def keptBy (s s' : State) (a : Nat) : Bool := { s'.agt a with told := [] } == { s.agt a with told := [] }

/-- N1. The tick keeps every agent that holds work once reap has run (its tasks' bases are those of the tasks it still
owns); reap takes no claim from a live owner whose job runs; an agent may claim back a task reap took from it (the 350k
fence does not refuse it); and GC removes only what is clean and on a protected ref (W1). -/
def N1 (c : Cfg) : Prop :=
  (∀ s a, Reachable c s → holdsWork c (reapLocks (reapTasks c s)) a = true → keptBy s (tickOf c s) a = true)
  ∧ (∀ s t o, Reachable c s → (s.tk t).st = .claimed → (s.tk t).owner = some o → (s.agt o).live = true →
      (s.agt o).bg = true → ((tickOf c s).tk t).owner = some o)
  ∧ (∀ s a t, Reachable c s → (s.tk t).reaped = some a → fenced c s a t = false)
  ∧ W1 c

-- ---------- the counterexamples ----------

/-- a tick from where the run ends changes agent a while it holds work -/
def n1Breaks (c : Cfg) (acts : List Action) (a : Nat) : Bool :=
  (run c acts).any fun s => holdsWork c (reapLocks (reapTasks c s)) a && !keptBy s (tickOf c s) a
/-- a tick from where the run ends takes claimed task t from its live owner o while o's job runs -/
def reapBreaks (c : Cfg) (acts : List Action) (t o : Nat) : Bool :=
  (run c acts).any fun s => (s.tk t).st == .claimed && (s.tk t).owner == some o && (s.agt o).live && (s.agt o).bg
    && ((tickOf c s).tk t).owner != some o
/-- where the run ends, reap took t from a and the fence refuses a's claim of it -/
def retakeBreaks (c : Cfg) (acts : List Action) (a t : Nat) : Bool :=
  (run c acts).any fun s => (s.tk t).reaped == some a && fenced c s a t

theorem not_N1_keep {c : Cfg} {acts : List Action} {a : Nat} (h : n1Breaks c acts a = true) : ¬ N1 c := by
  intro hN
  unfold n1Breaks at h
  cases e : run c acts with
  | none => simp [e] at h
  | some s =>
    simp only [e, Option.any_some, Bool.and_eq_true, Bool.not_eq_true'] at h
    have := hN.1 s a (reachable_of_run e) h.1
    rw [h.2] at this; cases this

theorem not_N1_reap {c : Cfg} {acts : List Action} {t o : Nat} (h : reapBreaks c acts t o = true) : ¬ N1 c := by
  intro hN
  unfold reapBreaks at h
  cases e : run c acts with
  | none => simp [e] at h
  | some s =>
    simp only [e, Option.any_some, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    exact h.2 (hN.2.1 s t o (reachable_of_run e) h.1.1.1.1 h.1.1.1.2 h.1.1.2 h.1.2)

theorem not_N1_fence {c : Cfg} {acts : List Action} {a t : Nat} (h : retakeBreaks c acts a t = true) : ¬ N1 c := by
  intro hN
  unfold retakeBreaks at h
  cases e : run c acts with
  | none => simp [e] at h
  | some s =>
    simp only [e, Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    rw [hN.2.2.1 s a t (reachable_of_run e) h.1] at h; cases h.2

/-- #10: agent 0 claims #1, starts a long job and stops; the lease lapses, and with `bgKeeps` off reap reopens #1 and
watchd spawns agent 1 onto it while the job runs -/
def pre10 : List Action := [.add [], .claim 0 1, .bgStart 0, .stop 0 false, .expire 1, .leave 1]
theorem not_N1_bgKeeps : ¬ N1 { bgKeeps := false } := not_N1_reap (by decide : reapBreaks { bgKeeps := false } pre10 1 0 = true)
/-- #11: reap took #1 from agent 0, whose context is big; with `retake` off the fence refuses it the task it held -/
def pre11 : List Action := [.add [], .claim 0 1, .stop 0 true, .expire 1, .tick]
theorem not_N1_retake : ¬ N1 { retake := false } := not_N1_fence (by decide : retakeBreaks { retake := false } pre11 0 1 = true)
/-- #12: agent 0 owns two worktrees; wt_map picks the landed one, the other has an uncommitted file; with `allWts` off
lifecycle ends it -/
def pre12 : List Action := twoWts.dropLast
theorem not_N1_allWts : ¬ N1 { nwts := 2, allWts := false } := not_N1_keep (by decide : n1Breaks { nwts := 2, allWts := false } pre12 0 = true)
/-- #26: agent 0 starts a long job (a build, a CI wait) and stops holding nothing; with `bgLives` off lifecycle ends it
mid-job: ending kills its terminal, and the job with it -/
def pre26 : List Action := [.bgStart 0, .stop 0 false, .age 0]
theorem not_N1_bgLives : ¬ N1 {} := not_N1_keep (by decide : n1Breaks {} pre26 0 = true)
/-- #27: spawned agent 0 (its worktree recorded) adds a second worktree, edits there, edits back in the first, lands that
and marks its task done; the second still holds an uncommitted file. With `ownAdded` off lifecycle sees the record and
agent.wt only, and ends it -/
def cfg27 : Cfg := { nwts := 2, recordedWorkspaces := true }
def pre27 : List Action := [.stop 0 false, .age 0, .tick, .add [], .tick, .boot 0, .git 0 (.add 0), .git 0 (.edit 0),
  .git 0 (.add 1), .git 0 (.edit 1), .git 0 (.edit 0), .git 0 (.commit 0), .git 0 (.land 0 0), .done 0 1 true,
  .stop 0 false, .age 0]
theorem not_N1_ownAdded : ¬ N1 cfg27 := not_N1_keep (by decide : n1Breaks cfg27 pre27 0 = true)

-- the same runs with each fix on: the tick keeps the agent, the claim, and the retake
example : n1Breaks { bgLives := true } pre26 0 = false := by decide
example : n1Breaks { cfg27 with ownAdded := true } pre27 0 = false := by decide
example : n1Breaks { nwts := 2 } pre12 0 = false := by decide
example : reapBreaks {} pre10 1 0 = false := by decide
example : retakeBreaks {} pre11 0 1 = false := by decide

-- ---------- the proof ----------

/-- with the fixes on, lifecycle calls no agent that holds work finished: it neither ends nor reuses it -/
theorem finished_of_holds {c : Cfg} (hbl : c.bgLives = true) (haw : c.allWts = true) (hoa : c.ownAdded = true)
    (hp : c.perTaskBase = true) {z : State} {a : Nat} (h : holdsWork c z a = true) : finished c z a = false := by
  have e : ∀ refs w, landedC c z.git refs w = z.git.landedIn refs w := fun _ _ => by simp [landedC, hp]
  simp only [holdsWork, Bool.and_eq_true, Bool.or_eq_true] at h
  obtain ⟨_, (hbg | hw) | ho⟩ := h
  · simp [finished, hbl, hbg]
  · have : unlanded c z a = true := by simp only [unlanded, e, hw, Bool.true_or]
    simp [finished, this]
  · have : unlanded c z a = true := by simp only [unlanded, e, ho, haw, hoa, Bool.or_true, Bool.and_true, Bool.true_and]
    simp [finished, this]

/-- lifecycle leaves a live agent it doesn't call finished as it was, but for what a digest told it -/
theorem lifecycle_keeps {c : Cfg} {z : State} {a : Nat} (hf : finished c z a = false) (hl : (z.agt a).live = true) :
    { (lifecycle c z).agt a with told := [] } = { z.agt a with told := [] } := by
  have he := (endFold_a (c := c) (z := z) (a := a) (by simp [hf])).1
  let P : State → Prop := fun y => { y.agt a with told := [] } = { z.agt a with told := [] } ∧ (y.agt a).live = true
  have hdig : P (c.agents.foldl (digStep c z) (endFold c z)) :=
    foldl_inv (digStep c z) P c.agents _ ⟨by rw [he], by rw [he]; exact hl⟩ (fun y b hy => by
      simp only [P] at hy ⊢
      unfold digStep; split
      · simp only [post_agt, agt_setAg]; split
        · exact hy
        · exact hy
      · exact hy)
  rw [lifecycle_eq]; split
  · exact hdig.1
  · exact (foldl_inv (spawnFor c (pool c z)) P c.tasks _ hdig (fun y t hy => by
      rcases spawnFor_agt c (pool c z) y t a with e | ⟨hn, _⟩
      · simp only [P] at hy ⊢
        rw [e]; exact hy
      · have := nextAgent_not_live hn; rw [hy.2] at this; cases this)).1

theorem reapTask_keeps {c : Cfg} {x : State} {t o u : Nat} (ho : (x.tk t).owner = some o) (hk : keeps c (x.agt o) = true) :
    (reapTask c x u).tk t = x.tk t := by
  by_cases hu : t = u
  · subst hu; unfold reapTask; simp [ho, hk]
  · exact reapTask_tk_ne hu

/-- lifecycle leaves a claimed task as it was: its owner holds it, so it is not ended, and it is not in the pool -/
theorem lifecycle_tk {c : Cfg} {z : State} {t o : Nat} (hst : (z.tk t).st = .claimed) (ho : (z.tk t).owner = some o) :
    (lifecycle c z).tk t = z.tk t := by
  have hfin : finished c z o = false := by simp [finished, idleFree, holds_of hst ho]
  have hpl : (pool c z).contains t = false := by simp [pool, claimable, startable, hst]
  have h2 : (endFold c z).tk t = z.tk t := by
    unfold endFold
    exact foldl_inv _ (fun y : State => y.tk t = z.tk t) c.agents z rfl (fun y b hy => by
      split
      · rename_i hh
        have hb : b ≠ o := by rintro rfl; simp [hfin] at hh
        rw [endAgent_tk, hy]; simp [held, ho, Ne.symm hb]
      · exact hy)
  have h3 : (c.agents.foldl (digStep c z) (endFold c z)).tk t = z.tk t :=
    foldl_inv (digStep c z) (fun y : State => y.tk t = z.tk t) c.agents _ h2 (fun y b hy => by
      unfold digStep; split
      · simp only [post_tk, setAg_tk]; exact hy
      · exact hy)
  rw [lifecycle_eq]; split
  · exact h3
  · exact foldl_inv _ (fun y : State => y.tk t = z.tk t) _ _ h3 (fun y t' hy => by
      by_cases e : t = t'
      · subst e; rw [spawnFor_not hpl]; exact hy
      · rw [spawnFor_tk_ne e]; exact hy)

/-- N1 with every fix on: PR #121 (`bgKeeps`, `retake`, reap as `idle`), PR #123 (`allWts`), board #15 (`bgLives`,
`ownAdded`), and sw-bases' per-task bases and split GC (`perTaskBase`, `splitGC`) -/
theorem N1_of (c : Cfg) (hrel : c.release = .idle) (hbk : c.bgKeeps = true) (hret : c.retake = true) (haw : c.allWts = true)
    (hbl : c.bgLives = true) (hoa : c.ownAdded = true) (hp : c.perTaskBase = true) (hs : c.splitGC = true) : N1 c := by
  refine ⟨fun s a _ h => ?_, fun s t o _ hst ho hl hbg => ?_, fun s a t _ h => ?_, W1_of c hs⟩
  · have hz : (reapLocks (reapTasks c s)).agt a = s.agt a := agt_of_ag (by simp) a
    have hl : ((reapLocks (reapTasks c s)).agt a).live = true := by
      simp only [holdsWork, Bool.and_eq_true] at h; exact h.1
    have := lifecycle_keeps (finished_of_holds hbl haw hoa hp h) hl
    obtain ⟨_, _, he⟩ := tickOf_ex c s; rw [he]
    simp only [keptBy, beq_iff_eq]
    show { (lifecycle c (reapLocks (reapTasks c s))).agt a with told := [] } = _
    rw [this, hz]
  · have hk : keeps c (s.agt o) = true := by simp [keeps, hrel, hbk, hl, hbg]
    have hr : (reapTasks c s).tk t = s.tk t := by
      unfold reapTasks
      exact (foldl_inv (reapTask c) (fun y : State => y.tk t = s.tk t ∧ y.ag = s.ag) c.tasks s ⟨rfl, rfl⟩
        (fun y u hy => ⟨by rw [reapTask_keeps (by rw [hy.1]; exact ho) (by rw [agt_of_ag hy.2]; exact hk), hy.1],
          by rw [reapTask_ag]; exact hy.2⟩)).1
    have hz : (reapLocks (reapTasks c s)).tk t = s.tk t := by rw [tk_of_task (reapLocks_task _), hr]
    obtain ⟨_, _, he⟩ := tickOf_ex c s; rw [he]
    show ((lifecycle c (reapLocks (reapTasks c s))).tk t).owner = some o
    rw [lifecycle_tk (by rw [hz]; exact hst) (by rw [hz]; exact ho), hz, ho]
  · simp [fenced, hret, h]

/-- N1 holds of the instance the replay runs -/
theorem replay_N1 : N1 replay := N1_of _ rfl rfl rfl rfl rfl rfl rfl rfl

end Swarm
