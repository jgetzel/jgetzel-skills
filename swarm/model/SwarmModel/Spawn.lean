import SwarmModel.Inbox

/-! Spawn reservation and launch failure (board #16). `swarm spawn --task N` reserves the name and the task in one
transaction (an agent row with no terminal, `hc` null, status idle, and the task claimed for it), makes the worktree,
then launches; a launch that fails is undone (`tasks.unreserve`: the row ended, the task open again). watchd's
auto-spawn keeps three meta rows: `spawn_backoff` (until when it launches nothing, and the failed name the retry
reuses), `spawn_fails` (the task and its failures in a row) and `spawn_halt` (the task it gave up on after
`SPAWN_FAILS`, until the task leaves the pool).

The model of the main instance (`State`, `step`) is unchanged; this layer adds the meta rows and two outcomes of the
tick's first launch: it works (`tick`, the model's spawns) or it fails (`fail`). `rollbackAll` is the fix: before it
only launch.sh's non-zero exit was undone, and an error raised before launch.sh ran (`launch_agent`'s `die` when it
can't write the agent's settings file) left the reservation: a live row with no terminal holding the task.

Sp1 (a failed launch leaves nothing behind) and Sp2 (its task is in the pool at once) are refuted with the switch off
in Findings.lean (#28, and #29: the leaked row's name is the one the retry reuses) and proved with it on here (`Sp1_of`,
`Sp2_of`); Sp3 (a backoff lifts on fair runs) holds either way (`Sp3_of`). -/

namespace Swarm
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure SCfg where
  sw : Cfg := {}
  /-- board #16: spawn undoes its reservation on any failure after it, an error raised before launch.sh runs as well
  as launch.sh's exit; before, only the exit -/
  rollbackAll : Bool := false
  /-- watchd's SPAWN_FAILS: failed launches of one task in a row before auto-spawn halts it -/
  maxFails : Nat := 5
  deriving DecidableEq, Repr, Inhabited

/-- the main instance's state and auto-spawn's meta rows -/
structure SWorld where
  s : State
  /-- spawn_backoff's time is ahead: auto-spawn launches nothing -/
  backoff : Bool := false
  /-- spawn_backoff's name: the slot of the last failed launch, whose name the next launch reuses -/
  bo : Option Nat := none
  /-- spawn_fails: the task and how many of its launches failed in a row -/
  fails : Nat × Nat := (0, 0)
  /-- spawn_halt -/
  halt : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- `lifecycle`, its spawns drawn from `gate` of the pool -/
def lifecycleG (c : Cfg) (gate : List Nat → List Nat) (s : State) : State :=
  let pl := pool c s
  let ended := c.agents.foldl (fun x a => if finished c s a && !reusable c s a then endAgent x a else x) s
  let told := c.agents.foldl (fun x a =>
    if reusable c s a && !pl.all (x.agt a).told.contains then
      post (setAg x a fun g => { g with told := pl ++ g.told }) ⟨none, a, false, .digest, 0⟩
    else x) ended
  if c.agents.any (reusable c s) then told else c.tasks.foldl (spawnFor c (gate pl)) told
def tickG (c : Cfg) (gate : List Nat → List Nat) (s : State) : State :=
  let r := reapLocks (reapTasks c s)
  { lifecycleG c gate r with git := gitTick c r }
theorem tickG_id (c : Cfg) (s : State) : tickG c id s = tickOf c s := rfl

/-- the tick with no spawn: reap, sweep, lifecycle's ends and digests -/
def noSpawn (c : Cfg) (s : State) : State := tickG c (fun _ => []) s
/-- auto_spawn runs: lifecycle found no reusable agent and the pool isn't empty -/
def reached (c : Cfg) (s : State) : Bool :=
  let r := reapLocks (reapTasks c s)
  !c.agents.any (reusable c r) && !(pool c r).isEmpty
/-- spawn_halt once auto_spawn has looked: lifted when its task left the pool -/
def haltNow (c : SCfg) (w : SWorld) : Option Nat :=
  if reached c.sw w.s && !w.backoff then w.halt.filter (pool c.sw (reapLocks (reapTasks c.sw w.s))).contains else w.halt
/-- the tasks auto-spawn tries this tick, in order -/
def tries (c : SCfg) (w : SWorld) (pl : List Nat) : List Nat :=
  if w.backoff then [] else pl.filter (some · != haltNow c w)
/-- auto-spawn's first launch this tick: its slot and task -/
def first (c : SCfg) (w : SWorld) : Option (Nat × Nat) :=
  let x := noSpawn c.sw w.s
  if reached c.sw w.s && members x < c.sw.roster then
    match (tries c w (pool c.sw (reapLocks (reapTasks c.sw w.s)))).head?, nextAgent c.sw x with
    | some t, some a => some (a, t)
    | _, _ => none
  else none
/-- the name the launch reuses is a live row's: agents.reserve refuses it ("is a live agent"), which auto_spawn takes
for a failed launch -/
def clash (c : SCfg) (w : SWorld) : Bool := w.bo.any fun b => ((noSpawn c.sw w.s).agt b).live

/-- what a raise before launch.sh left: the row live with no terminal (status idle, hc null, no waiter), its inbox new,
holding t -/
def leak (c : Cfg) (x : State) (a t : Nat) : State :=
  let x1 := setAg x a fun _ => { (default : Agent) with st := .idle, dead := true, recorded := c.recordedWorkspaces }
  claimed { x1 with
    cursor := x1.cursor.set a x1.log.length
    start := x1.start.set a x1.log.length
    seen := x1.seen.set a [] } a t
/-- auto_spawn's failure branch: a backoff with the failed name, one more failure of t in a row, the halt at maxFails -/
def failed (c : SCfg) (w : SWorld) (s' : State) (a t : Nat) : SWorld :=
  let n := if w.fails.1 == t then w.fails.2 + 1 else 1
  if n ≥ c.maxFails then { s := s', halt := some t }
  else { s := s', backoff := true, bo := some a, fails := (t, n), halt := haltNow c w }

def swhen (b : Bool) (w : SWorld) : Option SWorld := if b then some w else none

/-- watchd's tick, its launches working: a refused name fails the first (and stays the retry's name); else every spawn of the model's tick, and a
spawn clears the backoff and the failures -/
def stick (c : SCfg) (w : SWorld) : SWorld :=
  match first c w with
  | some (a, t) =>
    if clash c w then failed c w (noSpawn c.sw w.s) (w.bo.getD a) t
    else { s := tickG c.sw (tries c w) w.s, halt := haltNow c w }
  | none => { w with s := tickG c.sw (tries c w) w.s, halt := haltNow c w }
/-- the tick whose first launch fails: launch.sh exits non-zero, or (`raise`) launch_agent raises before running it -/
def sfail (c : SCfg) (w : SWorld) (raise : Bool) : Option SWorld :=
  match first c w with
  | some (a, t) => swhen (c.sw.watchd && !clash c w)
      (failed c w (if raise && !c.rollbackAll then leak c.sw (noSpawn c.sw w.s) a t else noSpawn c.sw w.s) a t)
  | none => none

inductive SAction where
  /-- the main instance's actions, all but its tick -/
  | sw (act : Action)
  | tick
  | fail (raise : Bool)
  /-- spawn_backoff's time passes -/
  | lapse
  deriving DecidableEq, Repr

def sstep (c : SCfg) (w : SWorld) : SAction → Option SWorld
  | .sw act => if act == .tick then none else (step c.sw w.s act).map fun s => { w with s := s }
  | .tick => let w' := stick c w; swhen (c.sw.watchd && w' != w) w'
  | .fail raise => sfail c w raise
  | .lapse => swhen w.backoff { w with backoff := false }

def sinit (c : SCfg) : SWorld := { s := init c.sw }

inductive SReachable (c : SCfg) : SWorld → Prop
  | init : SReachable c (sinit c)
  | step {w w' : SWorld} (act : SAction) : SReachable c w → sstep c w act = some w' → SReachable c w'

def srun (c : SCfg) (acts : List SAction) : Option SWorld := acts.foldlM (sstep c) (sinit c)

/-- what cli_model_spec.lua replays (Traces.lean) -/
def sreplay : SCfg := { sw := replay, rollbackAll := true }

-- ---------- Sp1: a failed launch leaves nothing behind ----------

theorem sfail_eq {c : SCfg} {w w' : SWorld} {raise : Bool} (h : sstep c w (.fail raise) = some w') :
    ∃ a t, first c w = some (a, t) ∧ clash c w = false ∧
      w' = failed c w (if raise && !c.rollbackAll then leak c.sw (noSpawn c.sw w.s) a t else noSpawn c.sw w.s) a t := by
  simp only [sstep, sfail] at h
  split at h
  · rename_i a t hf
    unfold swhen at h
    split at h
    · rename_i hc
      refine ⟨a, t, hf, ?_, (Option.some.inj h).symm⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc; exact hc.2
    · simp at h
  · simp at h

theorem failed_s (c : SCfg) (w : SWorld) (s' : State) (a t : Nat) : (failed c w s' a t).s = s' := by
  simp only [failed]; split <;> split <;> rfl

/-- Sp1. With the fix, the tick whose launch fails ends where the same tick with no spawn ends: no row of the failed
agent, no claim of it, no message to it -/
theorem Sp1_of {c : SCfg} (hfix : c.rollbackAll = true) {w w' : SWorld} {raise : Bool}
    (h : sstep c w (.fail raise) = some w') : w'.s = noSpawn c.sw w.s := by
  obtain ⟨a, t, -, -, rfl⟩ := sfail_eq h
  simp [failed_s, hfix]

-- ---------- Sp2: its task is in the pool at once ----------

theorem tk_endAgent_keep {x : State} {a u : Nat} (h : (x.tk u).st = .opn ∨ (x.tk u).st = .done) : (endAgent x a).tk u = x.tk u := by
  rw [endAgent_tk]
  have : held (x.tk u) a = false := by rcases h with h | h <;> simp [held, h]
  simp [this]

/-- lifecycle's ends and digests change no open or done task -/
theorem lifecycleG_nil_keep (c : Cfg) (z : State) {u : Nat} (h : (z.tk u).st = .opn ∨ (z.tk u).st = .done) :
    (lifecycleG c (fun _ => []) z).tk u = z.tk u := by
  have hend : ∀ (l : List Nat) (x : State), (x.tk u).st = .opn ∨ (x.tk u).st = .done →
      (l.foldl (fun x a => if finished c z a && !reusable c z a then endAgent x a else x) x).tk u = x.tk u := by
    intro l; induction l with
    | nil => intro x _; rfl
    | cons b bs ih =>
      intro x hx
      simp only [List.foldl_cons]
      have e : (if finished c z b && !reusable c z b then endAgent x b else x).tk u = x.tk u := by
        split
        · exact tk_endAgent_keep hx
        · rfl
      rw [ih _ (by rw [e]; exact hx), e]
  have htold : ∀ (l : List Nat) (x : State), (l.foldl (fun x a =>
      if reusable c z a && !(pool c z).all (x.agt a).told.contains then
        post (setAg x a fun g => { g with told := pool c z ++ g.told }) ⟨none, a, false, .digest, 0⟩
      else x) x).tk u = x.tk u := by
    intro l; induction l with
    | nil => intro x; rfl
    | cons b bs ih =>
      intro x
      simp only [List.foldl_cons]
      rw [ih]
      split <;> simp [State.tk]
  have hsp : ∀ (l : List Nat) (x : State), (l.foldl (spawnFor c []) x) = x := by
    intro l; induction l with
    | nil => intro x; rfl
    | cons b bs ih => intro x; simp only [List.foldl_cons]; rw [spawnFor_not (by simp), ih]
  unfold lifecycleG
  simp only []
  split
  · rw [htold, hend _ _ h]
  · rw [hsp, htold, hend _ _ h]

theorem noSpawn_startable {c : Cfg} {s : State} {t : Nat} (h : startable (reapLocks (reapTasks c s)) t = true) :
    startable (noSpawn c s) t = true := by
  generalize hz : reapLocks (reapTasks c s) = z at h
  have e : ∀ u, (z.tk u).st = .opn ∨ (z.tk u).st = .done → (noSpawn c s).tk u = z.tk u := by
    intro u hu
    have ht : (noSpawn c s).task = (lifecycleG c (fun _ => []) z).task := by rw [← hz]; rfl
    have e2 : (noSpawn c s).tk u = (lifecycleG c (fun _ => []) z).tk u := by simp only [State.tk, ht]
    rw [e2]
    exact lifecycleG_nil_keep c z hu
  simp only [startable, depsDone, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by rw [e t (Or.inl h1), h1], fun d hd => ?_⟩
  have hd' := h2 d (by rw [e t (Or.inl h1)] at hd; exact hd)
  rw [e d (Or.inr hd'), hd']

theorem first_pool {c : SCfg} {w : SWorld} {a t : Nat} (h : first c w = some (a, t)) :
    startable (reapLocks (reapTasks c.sw w.s)) t = true := by
  simp only [first] at h
  split at h
  · split at h
    · rename_i t' a' ht _
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have hm : t' ∈ tries c w (pool c.sw (reapLocks (reapTasks c.sw w.s))) := List.mem_of_mem_head? ht
      simp only [tries] at hm
      split at hm
      · simp at hm
      · have := (List.mem_filter.mp hm).1
        simp only [pool, List.mem_filter] at this
        exact this.2
    · simp at h
  · simp at h

/-- Sp2. With the fix, right after a failed launch its task is startable: back in the pool at once, not when the
leaked claim's 2 h lease lapses -/
theorem Sp2_of {c : SCfg} (hfix : c.rollbackAll = true) {w w' : SWorld} {raise : Bool} {a t : Nat}
    (hf : first c w = some (a, t)) (h : sstep c w (.fail raise) = some w') : startable w'.s t = true := by
  rw [Sp1_of hfix h]
  exact noSpawn_startable (first_pool hf)

-- ---------- Sp3: a backoff lifts ----------

structure SRun (c : SCfg) where
  st : Nat → SWorld
  act : Nat → SAction
  ok : ∀ n, sstep c (st n) (act n) = some (st (n + 1))

/-- the time a backoff waits passes: `lapse`, enabled at infinitely many steps, happens at infinitely many -/
def SRun.Fair {c : SCfg} (r : SRun c) : Prop :=
  (∀ N, ∃ n ≥ N, (sstep c (r.st n) .lapse).isSome) → ∀ N, ∃ n ≥ N, r.act n = .lapse

/-- Sp3. On a fair run a backoff lifts: auto-spawn launches again. (It holds with the switch off too: the backoff is
time; what the leak breaks is the launch after it, #29.) -/
theorem Sp3_of {c : SCfg} (r : SRun c) (hf : r.Fair) (n : Nat) : ∃ m ≥ n, (r.st m).backoff = false := by
  apply Classical.byContradiction
  intro hno'
  have hno : ∀ m ≥ n, (r.st m).backoff = true := fun m hm => by
    cases e : (r.st m).backoff
    · exact absurd ⟨m, hm, e⟩ hno'
    · rfl
  have hen : ∀ N, ∃ m ≥ N, (sstep c (r.st m) .lapse).isSome := fun N =>
    ⟨max N n, Nat.le_max_left .., by simp [sstep, swhen, hno _ (Nat.le_max_right ..)]⟩
  obtain ⟨m, hm, ha⟩ := hf hen n
  have := r.ok m
  rw [ha] at this
  simp only [sstep, swhen, hno m hm, if_true, Option.some.injEq] at this
  have h2 := hno (m + 1) (by omega)
  rw [← this] at h2
  exact absurd h2 (by simp)

end Swarm
