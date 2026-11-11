import SwarmModel.Model

/-! Lifted (rung 3, board #27): the Lua's pure decisions with a counterpart in the model, line for line on the rows
they read, and each proved to be the model's decision on its view of the state. `watchd.keeps` (reap: does a lapsed
claim's owner keep it), `watchd.fate` (lifecycle: keep, unclean, reuse or end an agent) and `msgs.wakes` (the
waiter). A Lua nil, or a NULL column, is `none`; a read the Lua makes through a callback (`f.claims()`, `cold()`) is
its answer, a `Bool`: what the read returns is the SQL's, rung 4. `DecideCases.lean` writes random inputs with these
functions' answers, which `../lua/test/decide_model_spec.lua` checks the Lua against. -/

namespace Swarm.Decide

/-- the agent row's columns the decisions read -/
structure ARow where
  ended : Option Nat := none
  status : String := "idle"
  hc : Option String := none
  stay : Option String := none
  lastActive : Option Int := none
  ctx : Option Nat := none
  waiter : Option Nat := none
  deriving Repr, Inhabited, DecidableEq

/-- watchd's `nz`: nil and "" are false -/
def nz : Option String → Bool
  | some s => s != ""
  | none => false

/-- watchd.keeps(o, bg, live_addrs): `live` is the live addresses, `none` when hc can't tell -/
def keepsL (o : Option ARow) (bg : Bool) (live : Option (List String)) : Bool :=
  match o with
  | none => false
  | some o => o.ended.isNone && (o.status != "idle" || bg)
      && !(live.isSome && nz o.hc && !(live.getD []).contains (o.hc.getD ""))

/-- an hc terminal as lifecycle reads it -/
structure Term where
  cwd : Option String := none
  status : String := "idle"
  deriving Repr, Inhabited, DecidableEq

/-- fate's reads, `f` in the Lua: `ours` is `f.ours(x.cwd)`, `alive` is `f.alive(a.waiter)` -/
structure Facts where
  ours : Bool
  claims : Bool
  locks : Bool
  unlanded : Bool
  job : Bool
  pool : Nat
  passedOver : Bool
  alive : Bool
  deriving Repr, Inhabited, DecidableEq

/-- the Lua's nil, "unclean", "reuse", "end" -/
inductive Verdict where | keep | unclean | reuse | end_
  deriving DecidableEq, Repr, Inhabited

/-- agents.SMALL_CTX -/
def smallCtx : Nat := 40000

/-- watchd.fate(a, t, x, has_terms, f) -/
def fateL (a : ARow) (t : Int) (x : Option Term) (hasTerms : Bool) (f : Facts) : Verdict :=
  if nz a.stay || a.status != "idle" || decide (t - a.lastActive.getD 0 < 120) || x.any (fun x => nz x.cwd && !f.ours)
      || (nz a.hc && hasTerms && x.all fun x => x.status != "idle" && x.status != "done")
      || f.claims || f.locks then .keep
  else if f.unlanded then .unclean
  else if f.job then .keep
  else if decide (a.ctx.getD 0 < smallCtx) && decide (f.pool > 0) && !f.passedOver && a.waiter.isSome && f.alive then .reuse
  else .end_

/-- a msg row's columns the waiter reads -/
structure MRow where
  kind : String
  urgent : Option Nat := none
  deriving Repr, Inhabited, DecidableEq

def MRow.urg (r : MRow) : Bool := r.urgent.getD 0 != 0

/-- msgs.wakes(rows, cold): the waking rows and whether one is urgent, or nil -/
def wakesL (rows : List MRow) (cold : Bool) : Option (List MRow × Bool) :=
  let (wake, urgent) := rows.foldl (fun (w, u) r => if r.kind != "notice" || r.urg then (w ++ [r], u || r.urg) else (w, u))
    ([], false)
  if !wake.isEmpty && (urgent || !cold) then some (wake, urgent) else none

-- ---------- the model's view ----------

def statusOf : ASt → String
  | .working => "working" | .blocked => "blocked" | .ended => "ended" | .idle => "idle" | .unborn => "unborn"

/-- slot a's row as reap reads it: none before it is born; its terminal's address is its slot, none if unbound -/
def keepRow (c : Cfg) (a : Nat) (g : Agent) : Option ARow :=
  if g.st == .unborn then none
  else some { ended := if g.st == .ended then some 0 else none, status := statusOf g.st,
              hc := if c.unbound.contains a then none else some (toString a) }

/-- `hc ls`'s live addresses: every slot whose terminal hasn't died; none when hc can't tell -/
def liveOf (c : Cfg) (s : State) : Option (List String) :=
  if c.hcSees then some ((c.agents.filter fun a => !(s.agt a).dead).map toString) else none

/-- reap's decision is the model's `keeps`, on the current Cfg (`release` idle, `bgKeeps`), except for an owner whose
bound terminal hc no longer lists: the Lua reopens its task, the model keeps it until `reapGone` (`keeps_gap`) -/
theorem keeps_lifted {c : Cfg} {s : State} {a : Nat} (hr : c.release = .idle) (hb : c.bgKeeps = true)
    (ha : a < c.nagents) (hd : ¬(c.hcSees = true ∧ c.unbound.contains a = false ∧ (s.agt a).dead = true)) :
    keepsL (keepRow c a (s.agt a)) (s.agt a).bg (liveOf c s) = keeps c (s.agt a) := by
  have hlive : (s.agt a).dead = false → c.hcSees = true →
      ((c.agents.filter fun b => !(s.agt b).dead).map toString).contains (toString a) = true := by
    intro hd' _
    simp only [List.contains_iff_mem, List.mem_map, List.mem_filter, Cfg.agents, List.mem_range]
    exact ⟨a, ⟨ha, by simp [hd']⟩, rfl⟩
  simp only [keeps, hr, hb, Bool.true_and, keepsL, keepRow, liveOf, Agent.live]
  cases hst : (s.agt a).st <;> cases hdd : (s.agt a).dead <;> cases hs : c.hcSees <;>
    cases hu : c.unbound.contains a <;> simp_all [statusOf, nz]

/-- the gap: a working owner whose bound terminal is gone keeps its lapsed claim in the model, not in the Lua -/
theorem keeps_gap : ∃ (c : Cfg) (s : State),
    keepsL (keepRow c 0 (s.agt 0)) (s.agt 0).bg (liveOf c s) = false ∧ keeps c (s.agt 0) = true :=
  ⟨{}, { (default : State) with ag := [{ (default : Agent) with st := .working, dead := true }] }, by decide, by decide⟩

/-- slot a's row as lifecycle reads it at time t, with no hc terminals (as the replay): `aged` is idle 2 min, `big` a
context of SMALL_CTX or more, `waiter` a waiter pid that is alive (`Env.waiter_alive`) -/
def fateRow (g : Agent) (t : Int) : ARow :=
  { status := statusOf g.st, lastActive := some (if g.aged then t - 120 else t),
    ctx := some (if g.big then smallCtx else 0), waiter := if g.waiter then some 1 else none,
    ended := if g.st == .ended then some 0 else none }

/-- fate's reads on the model: its claims and locks, its unlanded work, its background job, the pool, and passed over
(told of the whole pool, nothing unread: the model has no notices) -/
def factsOf (c : Cfg) (s : State) (a : Nat) : Facts :=
  { ours := true, claims := holds s a, locks := lockHeld s a, unlanded := unlanded c s a, job := (s.agt a).bg,
    pool := (pool c s).length,
    passedOver := (pool c s).all (s.agt a).told.contains && (unread s a).isEmpty, alive := true }

/-- the model's lifecycle verdict on a -/
def modelFate (c : Cfg) (s : State) (a : Nat) : Verdict :=
  if !idleFree s a then .keep else if unlanded c s a then .unclean else if c.bgLives && (s.agt a).bg then .keep
  else if reusable c s a then .reuse else .end_

theorem fate_core (g : Agent) (t : Int) (h1 h2 h3 : Bool) (pl u : List Nat) :
    fateL (fateRow g t) t none false ⟨true, h1, h2, h3, g.bg, pl.length, pl.all g.told.contains && u.isEmpty, true⟩ =
      if !(g.st == .idle && g.aged && !h1 && !h2) then .keep else if h3 then .unclean else if g.bg then .keep
      else if !g.big && !pl.isEmpty && !(pl.all g.told.contains && u.isEmpty) && g.waiter then .reuse else .end_ := by
  have h120 : t - (t - 120) = 120 := by omega
  have hpl : (0 < pl.length) = (pl.isEmpty = false) := by cases pl <;> simp
  rcases g with ⟨st, _, big, aged, _, _, _, _, _, _, bg⟩
  simp only [fateL, fateRow, nz, smallCtx, hpl]
  cases st <;> cases aged <;> cases big <;> cases h1 <;> cases h2 <;> cases h3 <;> cases bg <;>
    simp_all [statusOf, Int.sub_self]

/-- lifecycle's verdict is the model's, on the current Cfg (`bgLives`, board #15, as the replay), for an agent between no read and its write -/
theorem fate_lifted {c : Cfg} {s : State} {a : Nat} {t : Int} (hp : c.passedOver = true) (hw : c.waiterAlive = true)
    (hb : c.bgLives = true) (hr : (s.agt a).reading = 0) (hs : (s.agt a).snap = []) :
    fateL (fateRow (s.agt a) t) t none false (factsOf c s a) = modelFate c s a := by
  rw [factsOf, fate_core, modelFate, reusable, finished, idleFree]
  simp only [hp, hw, hb, hr, hs, beq_self_eq_true, List.isEmpty_nil, Bool.and_true, Bool.not_true, Bool.or_false,
    Bool.true_and]
  cases h1 : holds s a <;> cases h2 : lockHeld s a <;> cases h3 : unlanded c s a <;>
    cases ((s.agt a).st == .idle && (s.agt a).aged) <;> cases (s.agt a).bg <;> simp

theorem fate_end {c : Cfg} {s : State} {a : Nat} {t : Int} (hp : c.passedOver = true) (hw : c.waiterAlive = true)
    (hb : c.bgLives = true) (hr : (s.agt a).reading = 0) (hs : (s.agt a).snap = []) :
    fateL (fateRow (s.agt a) t) t none false (factsOf c s a) = .end_ ↔ ends c s a = true := by
  rw [fate_lifted hp hw hb hr hs, modelFate, ends, finished, hb]
  cases idleFree s a <;> cases unlanded c s a <;> cases reusable c s a <;> cases (s.agt a).bg <;> simp

theorem fate_reuse {c : Cfg} {s : State} {a : Nat} {t : Int} (hp : c.passedOver = true) (hw : c.waiterAlive = true)
    (hb : c.bgLives = true) (hr : (s.agt a).reading = 0) (hs : (s.agt a).snap = []) :
    fateL (fateRow (s.agt a) t) t none false (factsOf c s a) = .reuse ↔ reusable c s a = true := by
  rw [fate_lifted hp hw hb hr hs, modelFate, hb]
  have : reusable c s a = true → finished c s a = true := fun h => by
    simp only [reusable, Bool.and_eq_true] at h; exact h.1.1.1.1
  cases hi : idleFree s a <;> cases hu : unlanded c s a <;> cases hre : reusable c s a <;> cases hg : (s.agt a).bg <;>
    simp_all [finished]

def kindOf : Kind → String
  | .dm => "dm" | _ => "system"

/-- model message i as a msg row: none is a notice (notices go to the communicator, outside the model) -/
def msgRow (s : State) (i : Nat) : MRow := { kind := kindOf (s.msg i).kind, urgent := some (if (s.msg i).urgent then 1 else 0) }

theorem wakesL_all (rows : List MRow) (h : ∀ r ∈ rows, r.kind != "notice") (cold : Bool) :
    (wakesL rows cold).isSome = (!rows.isEmpty && (rows.any MRow.urg || !cold)) := by
  have : ∀ (l : List MRow) w u, (∀ r ∈ l, r.kind != "notice") →
      l.foldl (fun (w, u) r => if r.kind != "notice" || r.urg then (w ++ [r], u || r.urg) else (w, u)) (w, u)
        = (w ++ l, u || l.any MRow.urg) := by
    intro l; induction l with
    | nil => intro w u _; simp
    | cons r l ih =>
      intro w u hl
      simp only [List.foldl_cons, hl r (by simp), Bool.true_or, ↓reduceIte]
      rw [ih _ _ (fun x hx => hl x (by simp [hx]))]
      simp [Bool.or_assoc]
  simp only [wakesL, this rows [] false h, List.nil_append, Bool.false_or]
  split <;> simp_all

/-- the waiter wakes exactly when the model's `wakes` says, on the agent's unread messages and its `cold` -/
theorem wakes_lifted {s : State} {a : Nat} :
    (wakesL ((unread s a).map (msgRow s)) (s.agt a).cold).isSome = wakes s a := by
  rw [wakesL_all _ (by intro r hr; simp only [List.mem_map] at hr; obtain ⟨i, _, rfl⟩ := hr
                       simp only [msgRow]; cases (s.msg i).kind <;> decide)]
  simp only [wakes, List.isEmpty_map, List.any_map]
  have : (MRow.urg ∘ msgRow s) = fun i => (s.msg i).urgent := by
    funext i; simp only [Function.comp, MRow.urg, msgRow]; cases (s.msg i).urgent <;> rfl
  rw [this]; cases (unread s a).isEmpty <;> cases (s.agt a).cold <;> simp [Bool.or_comm]

end Swarm.Decide
