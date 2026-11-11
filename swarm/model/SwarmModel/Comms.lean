import SwarmModel.Model

/-! The communicator (board #8): several swarms (one per repo db, each a `State` of the model), hc terminals with a
Herdr space, each swarm's communicator row and its watchd. Theorem C1 is stated here; the runs that refute it on the
current `CCfg` (findings #22 to #24) are in Findings.lean. `ensureComms` is the fix (board #9, the Lua);
with it C1 holds (`C1_of`, below) and a dead communicator is replaced on fair runs (`comms_replaced`; board #10).

What it models, from the Lua: `swarm join` (agents.bind) binds the name's row to this terminal and refuses only a live
binding of that same row elsewhere (`--takeover` moves it); nothing looks at the terminal's other swarms, since each repo
has its own db. Watchd's reap ends any row, the communicator's too, whose terminal `hc ls` no longer lists, and nothing
binds a new one. Auto-spawn runs launch.sh, which opens the new tab in the space of `HC_TERMINAL_ID`: watchd's own
terminal, the one it was started from. A terminal's death ends the background jobs started from it (watchd is the
communicator's `run_in_background` Bash). -/

namespace Swarm

/-- the world: every swarm's instance, how many swarms, and each swarm's own space -/
structure CCfg where
  sw : Cfg := {}
  nswarms : Nat := 2
  /-- each swarm's own Herdr space (the space of its repo) -/
  home : List Nat := [0, 1]
  /-- the fix (board #9): watchd's tick, finding the swarm with work and no communicator bound to a live terminal in the
  swarm's space whose session is it, launches one there (a new terminal, joined `--takeover`); auto-spawn launches into
  the swarm's space, not watchd's terminal's; `swarm join` refuses a terminal outside the swarm's space, and one that is
  another swarm's communicator unless `--takeover` -/
  ensureComms : Bool := false
  deriving DecidableEq, Repr, Inhabited

structure Term where
  live : Bool
  space : Nat
  /-- the swarm whose communicator its session is: its `SWARM_NAME`, its ListAgents name, the db its `swarm wait` reads -/
  name : Option Nat
  deriving DecidableEq, Repr, Inhabited

structure World where
  sw : List State
  /-- each swarm's communicator row (meta.comms names it): the terminal it is bound to; none: no row, or ended -/
  comms : List (Option Nat)
  /-- each swarm's watchd: the terminal it was started from (its HC_TERMINAL_ID); none: not running -/
  wd : List (Option Nat)
  /-- hc terminals by address; an address is never reused -/
  term : List Term
  /-- the space each agent slot of each swarm was launched in -/
  spc : List (List Nat)
  deriving DecidableEq, Repr, Inhabited

def CCfg.swarms (c : CCfg) : List Nat := List.range c.nswarms
def CCfg.homeOf (c : CCfg) (i : Nat) : Nat := c.home.getD i 0
def World.st (w : World) (i : Nat) : State := w.sw.getD i default
def World.tm (w : World) (x : Nat) : Term := w.term.getD x default
def World.cm (w : World) (i : Nat) : Option Nat := w.comms.getD i none
def World.wdOf (w : World) (i : Nat) : Option Nat := w.wd.getD i none
def World.spaceOf (w : World) (i a : Nat) : Nat := (w.spc.getD i []).getD a 0

/-- what C1 asks a communicator for: some live agent or open task -/
def hasWork (s : State) : Bool := s.ag.any (·.live) || s.task.any (·.st == .opn)
/-- swarm i's communicator row is bound to a live terminal in the swarm's space, whose session is i's communicator -/
def commsOk (c : CCfg) (w : World) (i : Nat) : Bool :=
  (w.cm i).any fun x => (w.tm x).live && (w.tm x).space == c.homeOf i && (w.tm x).name == some i
/-- every live agent of swarm i was launched in the swarm's space -/
def spawnsHome (c : CCfg) (w : World) (i : Nat) : Bool :=
  c.sw.agents.all fun a => !((w.st i).agt a).live || w.spaceOf i a == c.homeOf i
/-- C1 of one swarm in one state -/
def c1 (c : CCfg) (w : World) (i : Nat) : Bool := (!hasWork (w.st i) || commsOk c w i) && spawnsHome c w i
def watchdUp (w : World) (i : Nat) : Bool := (w.wdOf i).any fun x => (w.tm x).live
def cwhen (b : Bool) (w : World) : Option World := if b then some w else none

def cinit (c : CCfg) : World where
  sw := c.swarms.map fun _ => init c.sw
  comms := c.swarms.map fun _ => none
  wd := c.swarms.map fun _ => none
  term := []
  spc := c.swarms.map fun i => c.sw.agents.map fun _ => c.homeOf i

/-- `SWARM_NAME=<i's communicator> swarm join [--takeover]` from terminal x -/
def cjoin (c : CCfg) (w : World) (i x : Nat) (tk : Bool) : Option World :=
  let t := w.tm x
  cwhen (i < c.nswarms && t.live
      && (w.cm i).all (fun y => y == x || tk || !(w.tm y).live)
      && (!c.ensureComms || (t.space == c.homeOf i && (tk || c.swarms.all fun j => j == i || w.cm j != some x))))
    { w with comms := w.comms.set i (some x), term := w.term.modify x ({ · with name := some i }) }
/-- `SWARM_COMMS=.. swarm watchd` started from terminal x; refused while one runs -/
def startWd (c : CCfg) (w : World) (i x : Nat) : Option World :=
  cwhen (i < c.nswarms && (w.tm x).live && !watchdUp w i) { w with wd := w.wd.set i (some x) }
/-- terminal x dies, and the watchd started from it -/
def cdie (w : World) (x : Nat) : Option World :=
  cwhen (w.tm x).live
    { w with term := w.term.modify x ({ · with live := false }), wd := w.wd.map fun o => if o == some x then none else o }
/-- watchd's tick of swarm i: reap ends a communicator row whose terminal is gone, the model's tick runs (its spawns land
in watchd's terminal's space), and with `ensureComms` a communicator is launched where C1 wants one -/
def tickW (c : CCfg) (w : World) (i : Nat) : World :=
  let s := w.st i
  let s' := tickOf c.sw s
  let sp := if c.ensureComms then c.homeOf i else (w.tm ((w.wdOf i).getD 0)).space
  let l := c.sw.agents.foldl (fun l a => if s'.agt a != s.agt a && (s'.agt a).boot then l.set a sp else l) (w.spc.getD i [])
  let w1 := { w with sw := w.sw.set i s', spc := w.spc.set i l,
                     comms := w.comms.set i ((w.cm i).filter fun y => (w.tm y).live) }
  if c.ensureComms && hasWork s' && !commsOk c w1 i then
    { w1 with term := w1.term ++ [⟨true, c.homeOf i, some i⟩], comms := w1.comms.set i (some w1.term.length) }
  else w1

inductive CAction where
  /-- swarm i's own model, all but its tick (`tick i`) -/
  | sw (i : Nat) (act : Action)
  /-- a terminal opens in space sp (the user, or a launch) -/
  | open (sp : Nat)
  | join (i x : Nat) (takeover : Bool)
  | watchd (i x : Nat)
  | die (x : Nat)
  | tick (i : Nat)
  deriving DecidableEq, Repr

def cstep (c : CCfg) (w : World) : CAction → Option World
  | .sw i act => if act == .tick || i ≥ c.nswarms then none else
      (step c.sw (w.st i) act).map fun s => { w with sw := w.sw.set i s }
  | .open sp => some { w with term := w.term ++ [⟨true, sp, none⟩] }
  | .join i x tk => cjoin c w i x tk
  | .watchd i x => startWd c w i x
  | .die x => cdie w x
  | .tick i => cwhen (watchdUp w i) (tickW c w i)

inductive CReachable (c : CCfg) : World → Prop
  | init : CReachable c (cinit c)
  | step {w w' : World} (act : CAction) : CReachable c w → cstep c w act = some w' → CReachable c w'

def crun (c : CCfg) (acts : List CAction) : Option World := acts.foldlM (cstep c) (cinit c)

theorem creachable_of_run {c : CCfg} {acts : List CAction} {w : World} (h : crun c acts = some w) : CReachable c w := by
  suffices ∀ (acts : List CAction) (w0 w : World), CReachable c w0 → acts.foldlM (cstep c) w0 = some w → CReachable c w from
    this acts _ w .init h
  intro acts
  induction acts with
  | nil => intro w0 w h0 h; simp [List.foldlM] at h; exact h ▸ h0
  | cons a as ih =>
    intro w0 w h0 h
    simp only [List.foldlM_cons, Option.bind_eq_bind] at h
    cases h1 : cstep c w0 a with
    | none => simp [h1] at h
    | some w1 => rw [h1] at h; exact ih w1 w (.step a h0 h1) h

/-- C1: whenever watchd ticks a swarm, the swarm it leaves behind, if it has a live agent or open task, has exactly one live
communicator (the row meta.comms names), bound to a live terminal in the swarm's own space whose session is that
communicator (its ListAgents name, the inbox its `swarm wait` reads); and every live agent was launched in that space. Said
of the state after each tick, since nothing can make a terminal's death and watchd's next look at it one step: `C1all`,
of every reachable state, is false with any fix (the run `c1allWindow`). -/
def C1 (c : CCfg) : Prop :=
  ∀ w i, CReachable c w → i < c.nswarms → watchdUp w i = true → c1 c (tickW c w i) i = true
/-- the same of every reachable state where watchd runs -/
def C1all (c : CCfg) : Prop := ∀ w i, CReachable c w → i < c.nswarms → watchdUp w i = true → c1 c w i = true

/-- the run ends where watchd runs for swarm i and its tick leaves C1 false -/
def c1Breaks (c : CCfg) (acts : List CAction) (i : Nat) : Bool :=
  i < c.nswarms && (crun c acts).any fun w => watchdUp w i && !c1 c (tickW c w i) i

theorem not_C1_of {c : CCfg} {acts : List CAction} {i : Nat} (h : c1Breaks c acts i = true) : ¬ C1 c := by
  intro hc
  unfold c1Breaks at h
  cases e : crun c acts with
  | none => simp [e] at h
  | some w =>
    simp only [e, Option.any_some, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨hi, hw, hb⟩ := h
    simp [hc w i (creachable_of_run e) hi hw] at hb

theorem not_C1all_of {c : CCfg} {acts : List CAction} {i : Nat}
    (h : (i < c.nswarms && (crun c acts).any fun w => watchdUp w i && !c1 c w i) = true) : ¬ C1all c := by
  intro hc
  cases e : crun c acts with
  | none => simp [e] at h
  | some w =>
    simp only [e, Option.any_some, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨hi, hw, hb⟩ := h
    simp [hc w i (creachable_of_run e) hi hw] at hb

/-- today a tick never binds a communicator: a swarm whose row is gone stays without one, whatever watchd does -/
theorem tick_binds_none {c : CCfg} {w : World} {i : Nat} (h : c.ensureComms = false) (hw : w.cm i = none) :
    (tickW c w i).cm i = none := by
  simp [tickW, h, World.cm, List.getD_eq_getElem?_getD, List.getElem?_set]
  split <;> simp_all [World.cm, List.getD_eq_getElem?_getD]

-- ---------- C1 with `ensureComms` (board #10) ----------

/-- what every reachable world keeps: a state and a communicator row per swarm, and with the fix the spaces agents were
launched in never change -/
structure CInv (c : CCfg) (w : World) : Prop where
  sw : w.sw.length = c.nswarms
  comms : w.comms.length = c.nswarms
  spc : c.ensureComms = true → w.spc = (cinit c).spc

theorem set_all_eq {l : List Nat} {v : Nat} (h : ∀ x ∈ l, x = v) (a : Nat) : l.set a v = l :=
  List.ext_getElem (by simp) fun n h1 h2 => by
    rw [List.getElem_set]; split
    · subst_vars; exact (h _ (List.getElem_mem h2)).symm
    · rfl

theorem foldl_fix {f : List Nat → Nat → List Nat} {l : List Nat} (h : ∀ a, f l a = l) :
    ∀ as : List Nat, as.foldl f l = l
  | [] => rfl
  | a :: as => by rw [List.foldl_cons, h]; exact foldl_fix h as

theorem cinit_spc_all (c : CCfg) (i : Nat) : ∀ x ∈ (cinit c).spc.getD i [], x = c.homeOf i := by
  simp only [cinit, CCfg.swarms, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : i < c.nswarms <;> simp [h]

theorem set_getD_self (l : List (List Nat)) (i : Nat) : l.set i (l.getD i []) = l := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < l.length
  · simp [List.getElem?_eq_getElem h]
  · simp [List.set_eq_of_length_le (Nat.le_of_not_lt h)]

/-- with the fix the tick launches into the swarm's space, where every agent already was -/
theorem tickW_spc {c : CCfg} {w : World} (hc : c.ensureComms = true) (hs : w.spc = (cinit c).spc) (i : Nat) :
    (tickW c w i).spc = w.spc := by
  have hall : ∀ x ∈ w.spc.getD i [], x = c.homeOf i := by rw [hs]; exact cinit_spc_all c i
  unfold tickW; simp only [hc, ite_true]
  rw [foldl_fix (l := w.spc.getD i []), set_getD_self]
  · split <;> rfl
  · intro a; split
    · exact set_all_eq hall a
    · rfl

theorem cinv_tickW {c : CCfg} {w : World} (h : CInv c w) (i : Nat) : CInv c (tickW c w i) where
  sw := by unfold tickW; split <;> simp [apply_ite (f := World.sw), h.sw]
  comms := by unfold tickW; split <;> simp [apply_ite (f := World.comms), apply_ite (f := List.length), h.comms]
  spc := fun hc => (tickW_spc hc (h.spc hc) i).trans (h.spc hc)

theorem cinv_of_reachable {c : CCfg} {w : World} (h : CReachable c w) : CInv c w := by
  induction h with
  | init => exact ⟨by simp [cinit, CCfg.swarms], by simp [cinit, CCfg.swarms], fun _ => rfl⟩
  | step act _ hs ih =>
    cases act with
    | sw i a =>
      simp only [cstep] at hs; split at hs; · simp at hs
      obtain ⟨s, -, rfl⟩ := Option.map_eq_some_iff.mp hs
      exact ⟨by simp [ih.sw], ih.comms, ih.spc⟩
    | «open» sp => simp only [cstep, Option.some.injEq] at hs; subst hs; exact ⟨ih.sw, ih.comms, ih.spc⟩
    | join i x tk =>
      simp only [cstep, cjoin, cwhen] at hs; split at hs <;> simp at hs; subst hs
      exact ⟨ih.sw, by simp [ih.comms], ih.spc⟩
    | watchd i x =>
      simp only [cstep, startWd, cwhen] at hs; split at hs <;> simp at hs; subst hs; exact ⟨ih.sw, ih.comms, ih.spc⟩
    | die x =>
      simp only [cstep, cdie, cwhen] at hs; split at hs <;> simp at hs; subst hs; exact ⟨ih.sw, ih.comms, ih.spc⟩
    | tick i =>
      simp only [cstep, cwhen] at hs; split at hs <;> simp at hs; subst hs; exact cinv_tickW ih i

/-- C1 with `ensureComms`: after every tick a swarm with work has its communicator, live, at home and in session, and
every agent was launched at home -/
theorem C1_of (c : CCfg) (hc : c.ensureComms = true) : C1 c := by
  intro w i hr hi _
  have h := cinv_of_reachable hr
  have home : spawnsHome c (tickW c w i) i = true := by
    simp only [spawnsHome, List.all_eq_true, World.spaceOf, tickW_spc hc (h.spc hc), h.spc hc]
    intro a ha
    simp [cinit, CCfg.swarms, Cfg.agents, hi, List.getD_eq_getElem?_getD] at ha ⊢
    simp [ha]
  simp only [c1, home, Bool.and_true]
  simp only [tickW, hc, ite_true]
  generalize tickOf c.sw (w.st i) = s'
  have hst : ∀ cm wd tm sp, (World.mk (w.sw.set i s') cm wd tm sp).st i = s' := by
    intro _ _ _ _; simp [World.st, List.getD_eq_getElem?_getD, h.sw, hi]
  split
  · simp [commsOk, World.cm, World.tm, List.getD_eq_getElem?_getD, h.comms, hi]
  · rename_i hw
    simp only [hst] at hw ⊢
    revert hw; cases hasWork s' <;> simp

-- ---------- C1, the liveness half: a dead communicator is replaced ----------

structure CRun (c : CCfg) where
  st : Nat → World
  act : Nat → CAction
  ok : ∀ n, cstep c (st n) (act n) = some (st (n + 1))

/-- watchd ticks: a swarm whose watchd runs at infinitely many steps is ticked at infinitely many -/
def CRun.Fair {c : CCfg} (r : CRun c) : Prop :=
  ∀ i, (∀ N, ∃ n ≥ N, watchdUp (r.st n) i = true) → ∀ N, ∃ n ≥ N, r.act n = .tick i

theorem CRun.reachable {c : CCfg} (r : CRun c) (h0 : CReachable c (r.st 0)) : ∀ n, CReachable c (r.st n)
  | 0 => h0
  | n + 1 => .step _ (r.reachable h0 n) (r.ok n)

/-- with `ensureComms`, on a fair run from a reachable world where swarm i's watchd keeps running, a swarm with work
whose communicator is gone (its terminal dead, its row reaped, another swarm's session in it) gets one again: from every
step on, some later step has it at home and in session -/
theorem comms_replaced {c : CCfg} (hc : c.ensureComms = true) (r : CRun c) (hf : r.Fair) (h0 : CReachable c (r.st 0))
    {i : Nat} (hi : i < c.nswarms) (hw : ∀ N, ∃ n ≥ N, watchdUp (r.st n) i = true) (N : Nat) :
    ∃ n ≥ N, c1 c (r.st n) i = true := by
  obtain ⟨n, hn, ha⟩ := hf i hw N
  have hs := r.ok n
  rw [ha] at hs
  simp only [cstep, cwhen] at hs
  split at hs
  · rename_i hu
    refine ⟨n + 1, by omega, ?_⟩
    simp only [Option.some.injEq] at hs
    rw [← hs]
    exact C1_of c hc _ _ (r.reachable h0 n) hi hu
  · simp at hs

end Swarm
