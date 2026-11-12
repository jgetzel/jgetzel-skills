import SwarmModel.Spawn
import SwarmModel.Fair

/-! Staffing order (board #91). tasks.pool orders the startable tasks: a red-main task first, then the lower priority
number, then the lower id. watchd's lifecycle reads the pool once at its top, and auto_spawn launches for its tasks in
that order; a launch takes seconds (a worktree, a terminal), and an agent's `task done` in the meantime can free a
dependent that outranks what is left of that read.

The model of the main instance (`State`, `step`) has no order and an atomic tick, so this layer adds both: each task's
`Rank`, and the tick's auto-spawn as steps of its own (`read`, then a `launch` per spawn, `rest`) between which the
instance's other actions run. `freshPool` is the fix: auto_spawn reads the pool again before each launch, and the
launch's claim checks, in its own transaction, that its task still heads it. Before, every launch of a tick walked
lifecycle's one read.

F1 (a launch is for the first task of the pool as it is at the launch, of those auto-spawn has not given up on) is
refuted with the switch off at the end (finding #37, `not_F1`) and proved with it on here (`launch_top`), of every step from any
world. `done_frees` and `release_waits` say what frees a dependent: its last dependency done, not released. -/

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- what the pool's order reads of a task's row: `title like 'main red:%'`, and `priority` (0 first; 2 unless given) -/
structure Rank where
  red : Bool := false
  priority : Nat := 2
  deriving DecidableEq, Repr, Inhabited

structure FCfg where
  sw : Cfg := {}
  /-- board #91: auto_spawn reads the pool again before each launch, and the launch's claim checks in its transaction
  that its task still heads it; before, every launch of a tick walked the pool lifecycle read at its top -/
  freshPool : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- the main instance's state, each task's rank, and auto-spawn's loop and meta rows -/
structure FWorld where
  s : State
  /-- each task's rank (index t; the default past the end) -/
  rank : List Rank := []
  /-- auto_spawn's loop runs: the pool lifecycle read at its top, in order -/
  walk : Option (List Nat) := none
  /-- spawn_backoff's time is ahead: auto-spawn launches nothing -/
  backoff : Bool := false
  /-- spawn_halt: the task auto-spawn gave up on -/
  halt : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

def FWorld.rk (w : FWorld) (t : Nat) : Rank := w.rank.getD t default

/-- tasks.pool's `order by title like 'main red:%' desc, priority, id`: h is before l -/
def before (w : FWorld) (h l : Nat) : Bool :=
  ((w.rk h).red && !(w.rk l).red) ||
    ((w.rk h).red == (w.rk l).red &&
      (decide ((w.rk h).priority < (w.rk l).priority) || ((w.rk h).priority == (w.rk l).priority && decide (h < l))))

def ins (w : FWorld) (t : Nat) : List Nat → List Nat
  | [] => [t]
  | u :: us => if before w u t then u :: ins w t us else t :: u :: us
/-- the tasks in the pool's order -/
def ranked (w : FWorld) (pl : List Nat) : List Nat := pl.foldr (ins w) []

/-- the task auto_spawn's next launch is for: the first it has not given up on, of the pool as it is now (`freshPool`),
or of lifecycle's read, there the first whose reserve does not lose -/
def next (c : FCfg) (w : FWorld) : Option Nat :=
  if c.freshPool then (ranked w (pool c.sw w.s)).find? (some · != w.halt)
  else (w.walk.getD []).find? fun t => some t != w.halt && claimable w.s t

def fwhen (b : Bool) (w : FWorld) : Option FWorld := if b then some w else none

inductive FAction where
  /-- the main instance's actions, all but its tick -/
  | sw (act : Action)
  /-- a task's place in the order changes: `swarm task priority`, or a task added with its title and `-p` -/
  | rank (t : Nat) (r : Rank)
  /-- the tick up to auto_spawn's loop: reap, lifecycle's read of the pool, its ends and digests; the loop starts if no
  agent is reusable, the pool is not empty and no backoff holds -/
  | read
  /-- one launch of the loop, for task t -/
  | launch (t : Nat)
  /-- a launch fails: the loop ends in a backoff, and (`halts`) auto-spawn gives up on the task -/
  | fail (halts : Bool)
  /-- the loop ends -/
  | rest
  /-- spawn_backoff's time passes -/
  | lapse
  deriving DecidableEq, Repr

def fstep (c : FCfg) (w : FWorld) : FAction → Option FWorld
  | .sw act => if act == .tick then none else (step c.sw w.s act).map fun s => { w with s := s }
  | .rank t r => some { w with rank := (w.rank ++ List.replicate (t + 1 - w.rank.length) default).set t r }
  | .read =>
    let r := reapLocks (reapTasks c.sw w.s)
    let loops := reached c.sw w.s && !w.backoff
    fwhen (c.sw.watchd && w.walk.isNone)
      { w with
        s := noSpawn c.sw w.s
        walk := if loops then some (ranked w (pool c.sw r)) else none
        halt := if loops then w.halt.filter (pool c.sw r).contains else w.halt }
  | .launch t =>
    fwhen (w.walk.isSome && !w.backoff && members w.s < c.sw.roster && (nextAgent c.sw w.s).isSome && next c w == some t)
      { w with s := spawnFor c.sw [t] w.s t }
  | .fail halts =>
    match next c w with
    | some t => fwhen (w.walk.isSome && !w.backoff) { w with walk := none, backoff := true, halt := if halts then some t else w.halt }
    | none => none
  | .rest => fwhen w.walk.isSome { w with walk := none }
  | .lapse => fwhen w.backoff { w with backoff := false }

def finit (c : FCfg) : FWorld := { s := init c.sw }
def frun (c : FCfg) (acts : List FAction) : Option FWorld := acts.foldlM (fstep c) (finit c)

-- ---------- the order ----------

theorem before_spec (w : FWorld) (h l : Nat) : before w h l = true ↔
    ((w.rk h).red = true ∧ (w.rk l).red = false) ∨
      ((w.rk h).red = (w.rk l).red ∧
        ((w.rk h).priority < (w.rk l).priority ∨ ((w.rk h).priority = (w.rk l).priority ∧ h < l))) := by
  simp [before]

theorem before_asymm {w : FWorld} {h l : Nat} (hb : before w h l = true) : before w l h = false := by
  cases e : before w l h
  · rfl
  · rw [before_spec] at hb e
    rcases hb with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases e with ⟨a', b'⟩ | ⟨a', b'⟩ <;> simp_all <;> omega

/-- two tasks are one, or one is before the other -/
theorem before_total (w : FWorld) (h l : Nat) : h = l ∨ before w h l = true ∨ before w l h = true := by
  simp only [before_spec]
  cases e1 : (w.rk h).red <;> cases e2 : (w.rk l).red <;> simp <;> omega

/-- not before is transitive -/
theorem nbefore_trans {w : FWorld} {a b d : Nat} (h1 : before w b a = false) (h2 : before w d b = false) :
    before w d a = false := by
  cases e : before w d a
  · rfl
  · have n1 : ¬ _ := fun x => by rw [(before_spec w b a).mpr x] at h1; exact Bool.noConfusion h1
    have n2 : ¬ _ := fun x => by rw [(before_spec w d b).mpr x] at h2; exact Bool.noConfusion h2
    rw [before_spec] at e
    revert n1 n2 e
    cases (w.rk a).red <;> cases (w.rk b).red <;> cases (w.rk d).red <;> simp <;> omega

theorem mem_ins (w : FWorld) (t x : Nat) (l : List Nat) : x ∈ ins w t l ↔ x = t ∨ x ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons u us ih =>
    simp only [ins]; split
    · simp only [List.mem_cons, ih]; constructor <;> (intro h; rcases h with h | h | h <;> simp [h])
    · simp only [List.mem_cons]

theorem mem_ranked (w : FWorld) (x : Nat) (pl : List Nat) : x ∈ ranked w pl ↔ x ∈ pl := by
  induction pl with
  | nil => simp [ranked]
  | cons u us ih => simp only [ranked, List.foldr_cons, mem_ins, List.mem_cons] at ih ⊢; rw [ih]

theorem ins_sorted (w : FWorld) (t : Nat) (l : List Nat) (h : l.Pairwise fun a b => before w b a = false) :
    (ins w t l).Pairwise fun a b => before w b a = false := by
  induction l with
  | nil => simp [ins]
  | cons u us ih =>
    rw [List.pairwise_cons] at h
    simp only [ins]; split
    · rename_i hb
      rw [List.pairwise_cons]
      refine ⟨fun x hx => ?_, ih h.2⟩
      rcases (mem_ins ..).mp hx with rfl | hx
      · exact before_asymm hb
      · exact h.1 x hx
    · rename_i hb
      have hb' : before w u t = false := by simpa using hb
      rw [List.pairwise_cons, List.pairwise_cons]
      exact ⟨fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hb'
        · exact nbefore_trans hb' (h.1 x hx), h⟩

theorem ranked_sorted (w : FWorld) (pl : List Nat) : (ranked w pl).Pairwise fun a b => before w b a = false := by
  induction pl with
  | nil => simp [ranked]
  | cons u us ih => exact ins_sorted w u _ ih

/-- the first of a sorted list that passes p: nothing that passes p is before it -/
theorem find_top {w : FWorld} {p : Nat → Bool} {l : List Nat} {t : Nat}
    (hs : l.Pairwise fun a b => before w b a = false) (hf : l.find? p = some t) :
    t ∈ l ∧ p t = true ∧ ∀ h ∈ l, p h = true → before w h t = false := by
  induction l with
  | nil => simp at hf
  | cons u us ih =>
    rw [List.pairwise_cons] at hs
    rw [List.find?_cons] at hf
    split at hf
    · rename_i hp
      obtain rfl := Option.some.inj hf
      refine ⟨List.mem_cons_self .., hp, fun h hh _ => ?_⟩
      rcases List.mem_cons.mp hh with rfl | hh
      · cases e : before w h h
        · rfl
        · exact absurd (before_asymm e) (by rw [e]; simp)
      · exact hs.1 h hh
    · rename_i hp
      obtain ⟨hm, hpt, hall⟩ := ih hs.2 hf
      refine ⟨List.mem_cons_of_mem _ hm, hpt, fun h hh hph => ?_⟩
      rcases List.mem_cons.mp hh with rfl | hh
      · rw [hph] at hp; exact absurd hp (by simp)
      · exact hall h hh hph

-- ---------- F1: a launch is for the top of the pool ----------

theorem launch_eq {c : FCfg} {w w' : FWorld} {l : Nat} (h : fstep c w (.launch l) = some w') :
    w.backoff = false ∧ next c w = some l := by
  simp only [fstep, fwhen] at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hc
    exact ⟨hc.1.1.1.2, hc.2⟩
  · simp at h

/-- F1. With the fix, a launch is for a task of the pool that auto-spawn has not given up on, and no such task is
before it in the pool's order: the pool as it is at the launch, whatever was done since lifecycle read it -/
theorem launch_top {c : FCfg} (hfix : c.freshPool = true) {w w' : FWorld} {l : Nat}
    (h : fstep c w (.launch l) = some w') :
    (l ∈ pool c.sw w.s ∧ w.halt ≠ some l) ∧
      ∀ t, t ∈ pool c.sw w.s → w.halt ≠ some t → before w t l = false := by
  have hn := (launch_eq h).2
  simp only [next, hfix, ite_true] at hn
  obtain ⟨hm, hp, hall⟩ := find_top (ranked_sorted w _) hn
  refine ⟨⟨(mem_ranked ..).mp hm, fun e => by simp [e] at hp⟩, fun t ht hh => ?_⟩
  exact hall t ((mem_ranked ..).mpr ht) (by simpa using fun e => hh e.symm)

-- ---------- what frees a dependent ----------

theorem stopped_unbelieve (s : State) (a t u : Nat) : stopped (unbelieve s a t) u = stopped s u := by
  have ha : ∀ o, active ((unbelieve s a t).agt o) = active (s.agt o) := fun o => by
    simp only [unbelieve]; rw [agt_setAg]; split <;> simp_all [active]
  have hc : ∀ o, (unbelieve s a t).cur o = s.cur o := fun o => by simp [State.cur]
  unfold stopped
  rw [unbelieve_tk]
  cases (s.tk u).stopTo with
  | none => rfl
  | some o => simp only [ha, hc]

/-- `task done` of x puts in the pool an open task that is not stopped and waits on nothing else -/
theorem done_frees {c : FCfg} {w w' : FWorld} {a x h : Nat} {ev : Bool}
    (hs : fstep c w (.sw (.done a x ev)) = some w') (hm : h ∈ c.sw.tasks) (ho : (w.s.tk h).st = .opn)
    (hst' : ¬ stopped w.s h = true) (hd : ∀ d ∈ (w.s.tk h).deps, d = x ∨ (w.s.tk d).st = .done) :
    h ∈ pool c.sw w'.s := by
  have hst : stopped w.s h = false := by simpa using hst'
  simp only [fstep] at hs
  split at hs
  · simp at hs
  · simp only [Option.map_eq_some_iff] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    simp only [step, done, when] at hs'
    split at hs'
    · rename_i hc
      obtain rfl := Option.some.inj hs'
      simp only [Bool.and_eq_true, ownsClaimed, beq_iff_eq] at hc
      have hx : (w.s.tk x).st = .claimed := hc.1.2.1
      have hne : h ≠ x := fun e => by rw [e, hx] at ho; exact TSt.noConfusion ho
      have hxa : ((logEv w.s (.done x)).tk x).st ≠ .absent := by rw [logEv_tk, hx]; exact fun e => TSt.noConfusion e
      have hk : ∀ u, u ≠ x → (unbelieve (setTask (logEv w.s (.done x)) x
          ({ · with st := .done, lease := false, ev := ev })) a x).tk u = w.s.tk u := fun u hu => by
        rw [unbelieve_tk, tk_setTask_ne hu, logEv_tk]
      have hkx : ((unbelieve (setTask (logEv w.s (.done x)) x
          ({ · with st := .done, lease := false, ev := ev })) a x).tk x).st = .done := by
        rw [unbelieve_tk, tk_setTask_self hxa]
      simp only [pool, List.mem_filter, claimable, startable, depsDone, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
        Bool.not_eq_true']
      refine ⟨hm, ⟨by rw [hk h hne]; exact ho, fun d hdm => ?_⟩, ?_⟩
      · rw [hk h hne] at hdm
        rcases hd d hdm with rfl | hdd
        · exact hkx
        · by_cases e : d = x
          · rw [e]; exact hkx
          · rw [hk d e]; exact hdd
      · rw [stopped_unbelieve, ← hst]
        simp only [stopped, tk_setTask_ne hne, logEv_tk, setTask_agt, logEv_agt, State.cur, setTask_cursor, logEv_cursor]
        rfl
    · simp at hs'

/-- `task release` of x frees nothing: a task that waits on x is not in the pool after it -/
theorem release_waits {c : FCfg} {w w' : FWorld} {a x h : Nat}
    (hs : fstep c w (.sw (.release a x)) = some w') (hd : x ∈ (w.s.tk h).deps) : h ∉ pool c.sw w'.s := by
  simp only [fstep] at hs
  split at hs
  · simp at hs
  · simp only [Option.map_eq_some_iff] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    simp only [step, release, when] at hs'
    split at hs'
    · rename_i hc
      obtain rfl := Option.some.inj hs'
      simp only [Bool.and_eq_true, ownsClaimed, beq_iff_eq] at hc
      have hx : (w.s.tk x).st = .claimed := hc.2.1
      have hxa : (w.s.tk x).st ≠ .absent := by rw [hx]; exact fun e => TSt.noConfusion e
      have hkx : ((unbelieve (setTask w.s x ({ · with st := .opn, owner := none, lease := false })) a x).tk x).st = .opn := by
        rw [unbelieve_tk, tk_setTask_self hxa]
      have hdeps : ((unbelieve (setTask w.s x ({ · with st := .opn, owner := none, lease := false })) a x).tk h).deps
          = (w.s.tk h).deps := by
        rw [unbelieve_tk]
        rcases tk_setTask_or w.s x h ({ · with st := .opn, owner := none, lease := false }) with e | ⟨_, e⟩ <;> rw [e]
      intro hp
      simp only [pool, List.mem_filter, claimable, startable, depsDone, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hp
      have := hp.2.1.2 x (by rw [hdeps]; exact hd)
      rw [hkx] at this
      exact TSt.noConfusion this
    · simp at hs'

theorem launch_or_before {c : FCfg} (hfix : c.freshPool = true) {w w' : FWorld} {l h : Nat}
    (hl : fstep c w (.launch l) = some w') (hp : h ∈ pool c.sw w.s) (hh : w.halt ≠ some h) :
    l = h ∨ before w l h = true := by
  rcases before_total w l h with e | e | e
  · exact Or.inl e
  · exact Or.inr e
  · rw [(launch_top hfix hl).2 h hp hh] at e; exact Bool.noConfusion e

-- ---------- finding #37: F1 without the fix ----------

-- #37, F1 (board #91). Auto-spawn walked the pool lifecycle read at the tick's top, and a launch takes seconds: a task
-- freed meanwhile waited behind lower-priority ones of that read. Agent 1 leaves (a free slot); #1, #2 and #3 are
-- added, #3 after #1 and at P0; agent 0 claims #1. The tick reads the pool, [#2]; agent 0 finishes #1, so #3 is in the
-- pool and before #2; the launch is for #2.
def cfg37 : FCfg := { sw := { nagents := 2, roster := 2, ntasks := 3 } }
def pre37 : List FAction := [.sw (.leave 1), .sw (.add []), .sw (.add []), .sw (.add [1]), .rank 3 ⟨false, 0⟩,
  .sw (.claim 0 1), .read, .sw (.done 0 1 true)]
example : (frun cfg37 pre37).any (fun w => w.walk == some [2] && pool cfg37.sw w.s == [2, 3] && before w 3 2
    && (fstep cfg37 w (.launch 2)).isSome && (fstep cfg37 w (.launch 3)).isNone) = true := by decide +kernel
-- with `freshPool` the launch reads the pool again: it is for #3, and none for #2 is enabled
example : (frun { cfg37 with freshPool := true } pre37).any (fun w =>
    (fstep { cfg37 with freshPool := true } w (.launch 3)).isSome && (fstep { cfg37 with freshPool := true } w (.launch 2)).isNone)
    = true := by decide +kernel

/-- #37, F1: with the switch off a launch is for a task that a task of the pool, not given up on, is before -/
theorem not_F1 : ¬ ∀ (w w' : FWorld) (l t : Nat), fstep cfg37 w (.launch l) = some w' → t ∈ pool cfg37.sw w.s →
    w.halt ≠ some t → before w t l = false := by
  intro h
  have hw := h ((frun cfg37 pre37).getD default) ((frun cfg37 (pre37 ++ [.launch 2])).getD default) 2 3 (by decide) (by decide) (by decide)
  revert hw; decide

end Swarm
