import LuaLean.Interp
import Lean

/-! A frame rule for calls (board #75): a call leaves alone a cell it cannot name. A cell is named by a running
function's environment, by a closure's (an upvalue), or by an address the semantics fixes (`CUR`, the running
coroutine). A local that no closure has captured is named by its own function alone, so no call it makes writes it.

`Own c P h`: the cell `c` of heap `h` holds a value with `P`, is no fixed cell, is in no closure's environment, and
the same holds of every heap a coroutine keeps to replay from (`Thr.hist`, `Thr.script`: a resume sets the heap to
one of them, DESIGN.md, *Coroutines*). `Keeps m Q`: from a heap where `c` is own, `m` ends (returning or not) in one
where it still is, a result with `Q` if it returns. `call_keeps`: every call keeps every own cell, whatever is
called, on every oracle and fuel. A run reads the cell back (`readCell`) with the value it had.

Values cannot name a cell: an address in a value (`.tbl`, `.fn`, `.thr`, `.cdata`, a number a builtin binds) is
used only as the object it should be, which a cell is not, so no forged one (an oracle can answer any value) writes
`c`. -/

set_option linter.unusedSimpArgs false

namespace Lua

/-- the heap a run ends in, returning or not -/
def heapOf {α} : EStateM.Result Err Heap α → Heap
  | .ok _ h => h
  | .error _ h => h

section own
variable (c : Nat) (P : Val → Prop)

/-- cell `c` is its function's own in `h` -/
inductive Own : Heap → Prop
  | intro {h : Heap} (cell : ∃ v, h[c]? = some (Obj.cell v) ∧ P v) (sys : 16 < c)
      (clo : ∀ (a : Nat) (cl : Clo), h[a]? = some (Obj.clo cl) → ∀ x ∈ cl.env, x.2 ≠ c)
      (thr : ∀ (a : Nat) (t : Thr Heap), h[a]? = some (Obj.thr t) → ∀ x ∈ t.hist ++ t.script, Own x.2) : Own h

/-- heaps a coroutine keeps, each keeping `c` own -/
def HeapsOk (l : List (List Val × Heap)) : Prop := ∀ x ∈ l, Own c P x.2

/-- an object that may be stored beside an own cell `c`: a closure that has not captured it, a coroutine whose
heaps keep it own -/
def ObjOk : Obj → Prop
  | .clo cl => ∀ x ∈ cl.env, x.2 ≠ c
  | .thr t => HeapsOk c P (t.hist ++ t.script)
  | _ => True

/-- a coroutine whose heaps keep `c` own -/
def ThrOk (t : Thr Heap) : Prop := HeapsOk c P (t.hist ++ t.script)

/-- an environment without `c` -/
def EnvOk (env : Env) : Prop := ∀ x ∈ env, x.2 ≠ c

/-- `m` keeps `c` own, its result with `Q` -/
def Keeps {α} (m : M α) (Q : α → Prop) : Prop :=
  ∀ h, Own c P h → match m h with
    | .ok a h' => Own c P h' ∧ Q a
    | .error _ h' => Own c P h'

end own

section rules
variable {c : Nat} {P : Val → Prop} {α β : Type} {m : M α} {Q R : α → Prop}

@[simp] theorem HeapsOk_nil : HeapsOk c P [] := by simp [HeapsOk]

@[simp] theorem HeapsOk_cons {x : List Val × Heap} {l : List (List Val × Heap)} :
    HeapsOk c P (x :: l) ↔ Own c P x.2 ∧ HeapsOk c P l := by simp [HeapsOk]

@[simp] theorem HeapsOk_append {l r : List (List Val × Heap)} :
    HeapsOk c P (l ++ r) ↔ HeapsOk c P l ∧ HeapsOk c P r := by
  simp only [HeapsOk, List.mem_append]; constructor
  · intro hh; exact ⟨fun x hx => hh x (.inl hx), fun x hx => hh x (.inr hx)⟩
  · rintro ⟨a, b⟩ x (hx | hx)
    · exact a x hx
    · exact b x hx

theorem Own.lt {h : Heap} (o : Own c P h) : c < h.size := by
  cases o with | intro cell _ _ _ => obtain ⟨v, e, _⟩ := cell; exact (Array.getElem?_eq_some_iff.1 e).1

theorem Own.sys16 {h : Heap} (o : Own c P h) : 16 < c := by cases o with | intro _ s _ _ => exact s

theorem Own.ne_obj {h : Heap} {a : Nat} {o : Obj} (ow : Own c P h) (e : h[a]? = some o) (no : ∀ v, o ≠ .cell v) :
    a ≠ c := by
  rintro rfl; cases ow with | intro cell _ _ _ => obtain ⟨v, e', _⟩ := cell; rw [e] at e'; exact no v (Option.some.inj e')

theorem Own.objOk {h : Heap} {a : Nat} {o : Obj} (ow : Own c P h) (e : h[a]? = some o) : ObjOk c P o := by
  cases ow with
  | intro _ _ hc ht => cases o <;> simp only [ObjOk] <;> first | trivial | exact hc _ _ e | exact ht _ _ e

/-- a write to a cell other than `c`, of an object that may stand beside it -/
theorem Own.set {h : Heap} {a : Nat} {o : Obj} (ow : Own c P h) (ne : a ≠ c) (ok : ObjOk c P o) :
    Own c P (h.set! a o) := by
  cases ow with
  | intro cell sys hc ht =>
  have get : ∀ b, (h.set! a o)[b]? = if a = b ∧ a < h.size then some o else h[b]? := by
    intro b; simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; split <;> simp_all
  refine .intro ?_ sys ?_ ?_
  · rw [get]; simp only [show ¬(a = c ∧ a < h.size) from fun hh => ne hh.1, ite_false]; exact cell
  · intro b cl e; rw [get] at e; split at e
    · cases e; exact ok
    · exact hc _ _ e
  · intro b t e; rw [get] at e; split at e
    · cases e; exact ok
    · exact ht _ _ e

theorem Own.push {h : Heap} {o : Obj} (ow : Own c P h) (ok : ObjOk c P o) : Own c P (h.push o) := by
  cases ow with
  | intro cell sys hc ht =>
  have get : ∀ b, (h.push o)[b]? = if b = h.size then some o else h[b]? := by
    intro b; rw [Array.getElem?_push]
  have lt : c < h.size := Own.lt (.intro cell sys hc ht)
  refine .intro ?_ sys ?_ ?_
  · rw [get]; simp only [show ¬(c = h.size) by omega, ite_false]; exact cell
  · intro b cl e; rw [get] at e; split at e
    · cases e; exact ok
    · exact hc _ _ e
  · intro b t e; rw [get] at e; split at e
    · cases e; exact ok
    · exact ht _ _ e

/-- the value of an own cell -/
theorem Own.cell {h : Heap} (ow : Own c P h) : ∃ v, h[c]? = some (.cell v) ∧ P v := by
  cases ow with | intro cell _ _ _ => exact cell

theorem Keeps.mono (r : Keeps c P m Q) (hq : ∀ a, Q a → R a) : Keeps c P m R := by
  intro h o; have := r h o; revert this; cases m h <;> simp only <;> intro x
  · exact ⟨x.1, hq _ x.2⟩
  · exact x

theorem Keeps.pure {a : α} (q : Q a) : Keeps c P (Pure.pure a : M α) Q := fun _ o => ⟨o, q⟩

theorem Keeps.throw {e : Err} : Keeps c P (throw e : M α) Q := fun _ o => o

theorem Keeps.throwThe {e : Err} : Keeps c P (throwThe Err e : M α) Q := fun _ o => o

theorem Keeps.bind {Q1 : α → Prop} {f : α → M β} {R : β → Prop} (hm : Keeps c P m Q1)
    (hf : ∀ a, Q1 a → Keeps c P (f a) R) : Keeps c P (m >>= f) R := by
  intro h o
  show match EStateM.bind m f h with | .ok a h' => _ | .error _ h' => _
  have := hm h o; simp only [EStateM.bind]; revert this
  cases m h with
  | ok a h1 => intro x; exact hf a x.2 h1 x.1
  | error e h1 => intro x; exact x

/-- a step whose result is not looked at -/
theorem Keeps.bindT {f : α → M β} {R : β → Prop} (hm : Keeps c P m fun _ => True)
    (hf : ∀ a, Keeps c P (f a) R) : Keeps c P (m >>= f) R := Keeps.bind hm fun a _ => hf a

theorem Keeps.seqRight {m' : M β} {R : β → Prop} (hm : Keeps c P m fun _ => True) (hf : Keeps c P m' R) :
    Keeps c P (m *> m') R := by
  show Keeps c P (m >>= fun _ => m') R; exact Keeps.bindT hm fun _ => hf

theorem Keeps.map {f : α → β} {R : β → Prop} (hm : Keeps c P m fun _ => True) (hr : ∀ a, R (f a)) :
    Keeps c P (f <$> m) R := by
  show Keeps c P (m >>= fun a => Pure.pure (f a)) R; exact Keeps.bindT hm fun a => Keeps.pure (hr a)


theorem Keeps.get : Keeps c P (MonadState.get : M Heap) (Own c P) := fun _ o => ⟨o, o⟩

theorem Keeps.getThe : Keeps c P (getThe Heap : M Heap) (Own c P) := fun _ o => ⟨o, o⟩

theorem Keeps.set {h1 : Heap} (o1 : Own c P h1) : Keeps c P (set h1 : M PUnit) fun _ => True := fun _ _ => ⟨o1, trivial⟩

theorem Keeps.modify {f : Heap → Heap} (hf : ∀ h, Own c P h → Own c P (f h)) :
    Keeps c P (modify f : M PUnit) fun _ => True := fun h o => ⟨hf h o, trivial⟩

theorem Keeps.tryCatch {k : Err → M α} (hm : Keeps c P m Q) (hk : ∀ e, Keeps c P (k e) Q) :
    Keeps c P (tryCatch m k) Q := by
  intro h o
  show match EStateM.tryCatch m k h with | .ok a h' => _ | .error _ h' => _
  have := hm h o; simp only [EStateM.tryCatch]; revert this
  cases m h with
  | ok a h1 => intro x; exact x
  | error e h1 => intro x; exact hk e h1 x

theorem Keeps.ite {b : Prop} [Decidable b] {x y : M α} (hx : b → Keeps c P x Q) (hy : ¬b → Keeps c P y Q) :
    Keeps c P (if b then x else y) Q := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

theorem Keeps.mapM {γ : Type} {l : List γ} {f : γ → M β} (hf : ∀ x, Keeps c P (f x) fun _ => True) :
    Keeps c P (l.mapM f) fun _ => True := by
  induction l with
  | nil => exact Keeps.pure trivial
  | cons x l ih =>
    simp only [List.mapM_cons]
    exact Keeps.bindT (hf x) fun _ => Keeps.bindT ih fun _ => Keeps.pure trivial

theorem Keeps.forIn_list {γ : Type} {l : List γ} {b : β} {f : γ → β → M (ForInStep β)}
    (hf : ∀ x b, Keeps c P (f x b) fun _ => True) : Keeps c P (forIn l b f) fun _ => True := by
  induction l generalizing b with
  | nil => exact Keeps.pure trivial
  | cons x l ih =>
    simp only [List.forIn_cons]
    refine Keeps.bindT (hf x b) fun r => ?_
    cases r with
    | done b' => exact Keeps.pure trivial
    | yield b' => exact ih

theorem Keeps.forIn_range {r : Std.Legacy.Range} {b : β} {f : Nat → β → M (ForInStep β)}
    (hf : ∀ x b, Keeps c P (f x b) fun _ => True) : Keeps c P (forIn r b f) fun _ => True := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']; exact Keeps.forIn_list hf

end rules

/-- a join point of a `do` block, kept by `Keeps` whatever it is given -/
theorem Keeps.jp {γ : Type} {v : γ → M α} {b : (γ → M α) → M α} (hv : ∀ y, Keeps c P (v y) Q)
    (hb : ∀ jp : γ → M α, (∀ y, Keeps c P (jp y) Q) → Keeps c P (b jp) Q) : Keeps c P (b v) Q := hb v hv

section tac
open Lean Meta Elab Tactic

/-- a `let`/`have` at the head of `m` in `Keeps c P m Q`: a join point (`γ → M α`) becomes a hypothesis that it
keeps (`Keeps.jp`), any other is substituted -/
elab "keeps_let" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let args := t.getAppArgs
  unless t.isAppOfArity ``Keeps 5 do throwError "keeps_let: not a Keeps goal"
  let m := args[3]!
  if m.isHeadBetaTarget then
    replaceMainGoal [← g.replaceTargetDefEq (mkAppN t.getAppFn #[args[0]!, args[1]!, args[2]!, m.headBeta, args[4]!])]
    return
  let (n, ty, v, b) ← match m with
    | .letE n ty v b _ => pure (n, ty, v, b)
    | _ => throwError "keeps_let: no let"
  let isJp ← forallTelescope ty fun _ r => do pure ((← whnfR r).isAppOf ``EStateM)
  if isJp && ty.isForall then
    let bfun := Expr.lam n ty b .default
    let e ← mkAppOptM ``Keeps.jp #[args[0]!, args[1]!, args[2]!, args[4]!, ty.bindingDomain!, v, bfun]
    match ← g.apply e with
    | [hv, hb] =>
      let (_, hv) ← hv.intro1P
      let (_, hb) ← hb.intro1P
      let (_, hb) ← hb.intro1P
      replaceMainGoal [hb, hv]
    | _ => throwError "keeps_let: Keeps.jp"
  else
    let newT := mkAppN t.getAppFn #[args[0]!, args[1]!, args[2]!, b.instantiate1 v, args[4]!]
    replaceMainGoal [← g.replaceTargetDefEq newT]

/-- every hypothesis that is a conjunction, a disjunction or an existential, split -/
partial def splitHyps (g : MVarId) : MetaM (List MVarId) := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if t.isAppOfArity ``And 2 || t.isAppOfArity ``Or 2 || t.isAppOfArity ``Exists 2 then
      let gs ← g.cases d.fvarId
      return (← gs.toList.mapM fun s => splitHyps s.mvarId).flatten
  pure [g]

elab "keeps_ands" : tactic => liftMetaTactic splitHyps

end tac

/-! The tactic: `keeps` takes a goal `Keeps c P m Q` apart, `m`'s binds, matches and conditions, down to the
functions with a lemma of their own (`keeps_leaf`: each lemma adds a `macro_rules`, the newest tried first) -/

/-- a lemma for the whole goal -/
syntax "keeps_leaf" : tactic
/-- a side condition: an address not `c`, an object or environment without it -/
syntax "keeps_side" : tactic

macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact (‹Keeps _ _ _ _›).mono fun _ _ => trivial)
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible assumption)
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact Keeps.get.mono fun _ _ => trivial)
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact Keeps.get)
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine Keeps.set ?_; keeps_side))
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact Keeps.throw)
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact Keeps.throwThe)

macro_rules | `(tactic| keeps_side) => `(tactic| (keeps_ands; simp_all +zetaDelta [ObjOk, EnvOk, ThrOk, HeapsOk_cons, HeapsOk_append] <;> omega))
/-- a side condition of a coroutine's heaps: membership in a list -/
macro "keeps_unf" : tactic => `(tactic| simp only [ObjOk, EnvOk, ThrOk, Prod.forall, List.mem_append] at *)
macro "keeps_mem" : tactic =>
  `(tactic| (keeps_ands; (try keeps_unf); intros; keeps_ands; (try subst_vars); solve_by_elim (maxDepth := 8)
    [Or.inl, Or.inr, List.mem_of_mem_tail, List.mem_append_left, List.mem_append_right, List.mem_singleton_self,
      List.mem_cons_self, List.mem_cons_of_mem]))
macro_rules | `(tactic| keeps_side) => `(tactic| keeps_mem)
macro_rules | `(tactic| keeps_side) => `(tactic| (keeps_ands; simp_all +zetaDelta [ObjOk, EnvOk, ThrOk, HeapsOk_cons, HeapsOk_append]; done))
macro_rules | `(tactic| keeps_side) => `(tactic| omega)
macro_rules | `(tactic| keeps_side) => `(tactic| assumption)
macro_rules | `(tactic| keeps_side) => `(tactic| trivial)

syntax "keeps_step" : tactic
macro_rules | `(tactic| keeps_step) => `(tactic| first
  | keeps_leaf
  | keeps_let
  | (with_reducible apply ‹∀ _, Keeps _ _ _ _›)
  | (with_reducible apply Keeps.bind; keeps_leaf; intro _ _)
  | (with_reducible refine Keeps.bindT ?_ fun _ => ?_)
  | (with_reducible refine Keeps.seqRight ?_ ?_)
  | (with_reducible refine Keeps.map ?_ fun _ => ?_)
  | (with_reducible refine Keeps.pure ?_; keeps_side)
  | (with_reducible refine Keeps.forIn_list fun _ _ => ?_)
  | (with_reducible refine Keeps.mapM fun _ => ?_)
  | (with_reducible refine Keeps.forIn_range fun _ _ => ?_)
  | (with_reducible refine Keeps.tryCatch ?_ fun _ => ?_)
  | split
  | keeps_side)

macro "keeps" : tactic => `(tactic| repeat' keeps_step)

section prims
variable {c : Nat} {P : Val → Prop}

theorem getObj_keeps {a : Nat} :
    Keeps c P (getObj a) fun o => ObjOk c P o ∧ ((∀ v, o ≠ .cell v) → a ≠ c) := by
  intro h ow
  simp only [getObj, bind, EStateM.bind, MonadState.get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  cases e : h[a]? with
  | none => simp only [die, throw, throwThe, MonadExceptOf.throw, EStateM.throw]; exact ow
  | some o => exact ⟨ow, ow.objOk e, fun no => ow.ne_obj e no⟩
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact getObj_keeps)

theorem getTbl_keeps {a : Nat} : Keeps c P (getTbl a) fun _ => a ≠ c := by
  unfold getTbl; refine Keeps.bind getObj_keeps fun o ho => ?_
  split
  · exact Keeps.pure (ho.2 (by simp))
  · exact Keeps.throw
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact getTbl_keeps)

theorem readCell_keeps {a : Nat} : Keeps c P (readCell a) fun _ => True := by
  unfold readCell; refine Keeps.bind getObj_keeps fun o _ => ?_; split
  · exact Keeps.pure trivial
  · exact Keeps.throw
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact readCell_keeps)

/-- an own cell read back: its value has `P` -/
theorem readCell_own : Keeps c P (readCell c) P := by
  intro h ow
  obtain ⟨v, e, pv⟩ := ow.cell
  simp only [readCell, getObj, bind, EStateM.bind, MonadState.get, getThe, MonadStateOf.get, EStateM.get, pure,
    EStateM.pure, e]
  exact ⟨ow, pv⟩

theorem modify_set_keeps {a : Nat} {o : Obj} (ne : a ≠ c) (ok : ObjOk c P o) :
    Keeps c P (modify fun h => h.set! a o : M PUnit) fun _ => True :=
  Keeps.modify fun _ ow => ow.set ne ok

macro_rules | `(tactic| keeps_leaf) => `(tactic| (with_reducible refine modify_set_keeps ?_ ?_ <;> keeps_side))

theorem putTbl_keeps {a : Nat} {t : Tbl} (ne : a ≠ c) : Keeps c P (putTbl a t) fun _ => True :=
  modify_set_keeps ne trivial
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine putTbl_keeps ?_; keeps_side))

theorem writeCell_keeps {a : Nat} {v : Val} (ne : a ≠ c) : Keeps c P (writeCell a v) fun _ => True :=
  modify_set_keeps ne trivial
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine writeCell_keeps ?_; keeps_side))

/-- a write to a fixed cell of the semantics (`CUR`, …), which `c` is not -/
theorem modify_sys_keeps {a : Nat} {o : Obj} (ha : a ≤ 16) (ok : ObjOk c P o) :
    Keeps c P (modify fun h => h.set! a o : M PUnit) fun _ => True :=
  Keeps.modify fun _ ow => ow.set (by have := ow.sys16; omega) ok

theorem writeCell_sys {a : Nat} {v : Val} (ha : a ≤ 16) : Keeps c P (writeCell a v) fun _ => True :=
  modify_sys_keeps ha trivial
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine writeCell_sys ?_; simp [CUR]))
macro "keeps_sys" : tactic => `(tactic| simp [ObjOk, CUR, LOG, STK, ERRF, CDECLS])
macro_rules | `(tactic| keeps_leaf) => `(tactic| (with_reducible refine modify_sys_keeps ?_ ?_) <;> keeps_sys)

theorem alloc_keeps {o : Obj} (ok : ObjOk c P o) : Keeps c P (alloc o) fun a => a ≠ c := by
  intro h ow
  simp only [alloc, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  exact ⟨ow.push ok, by have := ow.lt; omega⟩
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine alloc_keeps ?_; keeps_side))

end prims

end Lua
