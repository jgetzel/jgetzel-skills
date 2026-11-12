import SwarmModel.Lifted.Watchd
import LuaLean.Hoare
import LuaLean.FrameCall

/-! R2 (boards #67, #75): no Lua error escapes watchd's loop, on the real Lua. `M.loop`
(swarm/lua/swarm/watchd.lua, lifted: `Lifted/Watchd.lean`) is the loop: it calls `iteration` under `pcall` until an
iteration says why watchd exits (or `opts.once`). `iteration` runs the pass, an error's report and the pause, each
under `pcall`. Every external call they make (hc, git, sqlite, re, io) is in the pass, the report or the pause, so
here those are arbitrary: any value, which when called may return anything, raise anything, change the heap in any
way and call any effect, and the oracle is any oracle.

What is read after an arbitrary call is a local, a cell no closure has captured: the frame rule (`call_keeps`,
lua-lean's `LuaLean/FrameCall.lean`) keeps it (`Own`), with the value it had. A local is own from its allocation if
the heap then is `Fresh`: no coroutine holds a heap to replay (a replay could allocate at the local's address), and
no closure holds an address past the heap's end. -/

set_option linter.unusedSimpArgs false

namespace Swarm.LoopSafe
open Lua Swarm.Lifted.Watchd

/-- `m` from `h` ends in no Lua error: it returns, with `P` of its result, or stops (out of fuel, at an effect no
oracle answers, a yield, a stack query) -/
@[irreducible] def Ok {α} (m : M α) (h : Heap) (P : α → Heap → Prop) : Prop :=
  match m h with
  | .ok a h' => P a h'
  | .error e _ => e.isLua = false

section rules
variable {α β : Type} {m : M α} {h : Heap} {P Q : α → Heap → Prop}

theorem Ok.mono (r : Ok m h P) (hq : ∀ a h', P a h' → Q a h') : Ok m h Q := by
  unfold Ok at *; split <;> rename_i heq <;> rw [heq] at r
  · exact hq _ _ r
  · exact r

theorem Ok.pure {a : α} (p : P a h) : Ok (Pure.pure a : M α) h P := by unfold Ok; exact p

theorem Ok.bind {f : α → M β} {R : β → Heap → Prop} (r : Ok m h fun a h' => Ok (f a) h' R) : Ok (m >>= f) h R := by
  unfold Ok at *
  show match EStateM.bind m f h with | .ok a h' => R a h' | .error e _ => e.isLua = false
  simp only [EStateM.bind]
  cases hm : m h <;> simp only [hm] at r ⊢ <;> exact r

theorem Ok.tick {n : Nat} {k : Nat → M α} (r : ∀ n', n = n' + 1 → Ok (k n') h P) : Ok (Lua.tick n k) h P := by
  cases n with
  | zero => unfold Ok Lua.tick; rfl
  | succ n => unfold Lua.tick; exact r n rfl

theorem Ok.frame (r : Ok m h P) : Ok (Lua.frame m) h P := by
  unfold Ok at *; unfold Lua.frame
  cases hm : m h with
  | ok a h' => simp only [hm] at r ⊢; exact r
  | error e h' => simp only [hm] at r ⊢; cases e <;> simp_all [Err.isLua] <;> split <;> rfl

theorem Ok.onFrames {f : List Frame → List Frame} (r : Ok m h P) : Ok (Lua.onFrames f m) h P := by
  unfold Ok at *; unfold Lua.onFrames
  cases hm : m h with
  | ok a h' => simp only [hm] at r ⊢; exact r
  | error e h' => simp only [hm] at r ⊢; cases e <;> simp_all [Err.isLua]

theorem Ok.atSite {s : Site} (r : Ok m h P) : Ok (Lua.atSite s m) h P := by
  unfold Ok at *; unfold Lua.atSite
  cases hm : m h with
  | ok a h' => simp only [hm] at r ⊢; exact r
  | error e h' => simp only [hm] at r ⊢; cases e <;> simp_all [Err.isLua]

/-- pcall: whatever its first argument is and does when called -/
theorem Ok.pcall (I : Sem) (n : Nat) (f : Val) (as : List Val) :
    Ok (call I.srcs I.oracle I.tgt n (.prim "pcall" []) (f :: as)) h fun _ _ => True := by
  cases n with
  | zero => unfold Ok; rw [call]; rfl
  | succ n =>
  rw [call_prim]; refine Ok.frame (Ok.onFrames ?_)
  cases n with
  | zero => unfold Ok; rw [callPrim]; rfl
  | succ n =>
  rw [callPrim]
  show Ok (do anyArg 0 (f :: as); catchVal _ _ _) h _
  refine Ok.bind ?_
  unfold Ok anyArg; simp only [List.length_cons, Nat.zero_lt_succ, ↓reduceIte]
  unfold catchVal catchValF
  split <;> (try trivial) <;> (try rfl)
  rename_i h1 _
  generalize call I.srcs I.oracle I.tgt n ((f :: as).headD Val.nil) (f :: as).tail h1 = r
  rcases r with ⟨a, h2⟩ | ⟨e, h2⟩
  · trivial
  · rcases e with v | _ | _ | ⟨_ | k, m⟩ | _ | _ <;> trivial

theorem Ok.alloc {o : Obj} {Q : Nat → Heap → Prop} (p : Q h.size (h.push o)) : Ok (Lua.alloc o) h Q := by
  unfold Ok; exact p

theorem Ok.readCell {c : Nat} {v : Val} {Q : Val → Heap → Prop} (hc : h[c]? = some (.cell v)) (p : Q v h) :
    Ok (Lua.readCell c) h Q := by
  have e : Lua.readCell c h = .ok v h := by
    simp [Lua.readCell, getObj, Bind.bind, EStateM.bind, MonadState.get, getThe, MonadStateOf.get, EStateM.get, hc, Pure.pure, EStateM.pure]
  unfold Ok; rw [e]; exact p

theorem Ok.congr {m' : M α} (e : m h = m' h) (r : Ok m' h P) : Ok m h P := by unfold Ok at r ⊢; rw [e]; exact r

theorem push_keep {a : Nat} {o x : Obj} (e : h[a]? = some o) : (h.push x)[a]? = some o := by
  rw [Array.getElem?_push]; split
  · subst_vars; simp at e
  · exact e


/-! The shallow combinators `M.loop` and `iteration` are made of (`LuaLean/Shallow.lean`) -/

theorem Ok.eCell {c n : Nat} {w : Val} {Q : Val → Heap → Prop} (hc : h[c]? = some (.cell w)) (p : Q w h) :
    Ok (S.eCell c n) h Q := by
  unfold S.eCell; exact Ok.tick fun _ _ => Ok.readCell hc p

theorem Ok.lCons {e : S.SE} {l : S.SM} {n : Nat} {Q : List Val → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (e n') h fun w h1 => Ok (l n') h1 fun ws h2 => Q (w :: ws) h2) : Ok (S.lCons e l n) h Q := by
  unfold S.lCons; refine Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun w h1 r1 => Ok.bind (Ok.mono r1 fun ws h2 q => Ok.pure q))

theorem Ok.lLast {m : S.SM} {n : Nat} {Q : List Val → Heap → Prop} (r : ∀ n', n = n' + 1 → Ok (m n') h Q) :
    Ok (S.lLast m n) h Q := by unfold S.lLast; exact Ok.tick r

theorem Ok.mOne {e : S.SE} {n : Nat} {Q : List Val → Heap → Prop} (r : ∀ n', n = n' + 1 → Ok (e n') h fun w h1 => Q [w] h1) :
    Ok (S.mOne e n) h Q := by
  unfold S.mOne; exact Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun w h1 q => Ok.pure q)

theorem Ok.eAnd {a b : S.SE} {n : Nat} {Q : Val → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (a n') h fun x h1 => if x.truthy then Ok (b n') h1 Q else Q x h1) : Ok (S.eAnd a b n) h Q := by
  unfold S.eAnd; refine Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun x h1 q => ?_)
  split <;> simp_all <;> exact Ok.pure q

theorem Ok.block {q : S.SB} {n : Nat} {Q : Flow → Heap → Prop} (r : ∀ n', n = n' + 1 → Ok (q n') h Q) :
    Ok (S.block q n) h Q := by unfold S.block; exact Ok.tick r

theorem Ok.qLocal {es : S.SM} {k : Nat → List Val → M Flow} {n : Nat} {Q : Flow → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (es n') h fun vs h1 => Ok (k n' vs) h1 Q) : Ok (S.qLocal es k n) h Q := by
  unfold S.qLocal; exact Ok.tick fun n' hn => Ok.bind (r n' hn)

theorem Ok.mSite {s : Site} {m : S.SM} {n : Nat} {Q : List Val → Heap → Prop} (r : ∀ n', n = n' + 1 → Ok (m n') h Q) :
    Ok (S.mSite s m n) h Q := by unfold S.mSite; exact Ok.tick fun n' hn => Ok.atSite (r n' hn)

theorem Ok.mCall {I : Sem} {caller : Option Nat} {f : S.SE} {as : S.SM} {n : Nat} {Q : List Val → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (f n') h fun fv h1 => Ok (as n') h1 fun avs h2 =>
      Ok (fenvCall caller fv avs (call I.srcs I.oracle I.tgt n' fv avs)) h2 Q) : Ok (S.mCall I caller f as n) h Q := by
  unfold S.mCall; exact Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun _ _ r1 => Ok.bind r1)

/-- a statement that returns -/
theorem Ok.qStat_ret {s : S.SB} {g : String → M Flow} {q : S.SB} {n : Nat}
    (r : ∀ n', n = n' + 1 → Ok (s n') h fun fl _ => ∃ vs, fl = .ret vs) :
    Ok (S.qStat s g q n) h fun fl _ => ∃ vs, fl = .ret vs := by
  unfold S.qStat
  refine Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) ?_)
  rintro _ _ ⟨vs, rfl⟩; exact Ok.pure ⟨vs, rfl⟩

theorem Ok.sReturn {es : S.SM} {n : Nat} (r : ∀ n', n = n' + 1 → Ok (es n') h fun _ _ => True) :
    Ok (S.sReturn es n) h fun fl _ => ∃ vs, fl = .ret vs := by
  unfold S.sReturn
  exact Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun vs _ _ => Ok.pure ⟨vs, rfl⟩)

/-- the global `pcall`, the builtin, read from the running function's environment -/
theorem Ok.eGlob_pcall {I : Sem} {fn0 n : Nat} {c : Clo} {g : Tbl} {Q : Val → Heap → Prop}
    (hfn : h[fn0]? = some (.clo c)) (hg : h[c.fenv]? = some (.tbl g)) (hgm : g.mt = none)
    (hp : g.get (lstr "pcall") = .prim "pcall" []) (q : Q (.prim "pcall" []) h) : Ok (S.eGlob I fn0 "pcall" n) h Q := by
  unfold S.eGlob; refine Ok.tick fun n' _ => ?_
  cases n' with
  | zero =>
    have e : fenvOf fn0 h = .ok c.fenv h := fenvOf_ok hfn
    unfold Ok; simp only [Bind.bind, EStateM.bind, e]; rw [index]; rfl
  | succ n' =>
    have e : fenvOf fn0 h = .ok c.fenv h := fenvOf_ok hfn
    unfold Ok; simp only [Bind.bind, EStateM.bind, e]; rw [index]
    simp [lstr] at hp
    simp [noDump, Val.isDump, lstr, getTbl, getObj, hg, hp, held, weakOf, hgm, Val.isNil, Bind.bind, EStateM.bind,
      MonadState.get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure] at q ⊢
    exact q


/-! Own cells (`LuaLean/Frame.lean`) across a call -/

/-- the cells of `l`, each own with its predicate -/
def Owns (l : List (Nat × (Val → Prop))) (h : Heap) : Prop := ∀ x ∈ l, Own x.1 x.2 h

/-- a run that keeps every own cell keeps those of `l` -/
theorem Ok.keeps {l : List (Nat × (Val → Prop))} (r : Ok m h Q) (k : ∀ c P, Keeps c P m fun _ => True)
    (o : Owns l h) : Ok m h fun a h' => Q a h' ∧ Owns l h' := by
  unfold Ok at *
  have hk : ∀ x ∈ l, match m h with | .ok _ h' => Own x.1 x.2 h' ∧ True | .error _ h' => Own x.1 x.2 h' :=
    fun x hx => k x.1 x.2 h (o x hx)
  revert r hk; cases m h with
  | ok a h' => intro r hk; exact ⟨r, fun x hx => (hk x hx).1⟩
  | error e h' => intro r _; exact r

/-- a write of a cell of `l`, of a value with the predicates `l` gives the cell -/
theorem Owns.write {l : List (Nat × (Val → Prop))} {a : Nat} {v : Val} (o : Owns l h)
    (p : ∀ x ∈ l, x.1 = a → x.2 v) : Owns l (h.set! a (.cell v)) := by
  intro x hx
  by_cases e : x.1 = a
  · rw [← e]; exact (o x hx).setSelf (p x hx e)
  · exact (o x hx).set (Ne.symm e) trivial

/-- a cell of `l` read -/
theorem Ok.eCellOwn {l : List (Nat × (Val → Prop))} {c n : Nat} {R : Val → Prop} {Q : Val → Heap → Prop}
    (o : Owns l h) (hx : (c, R) ∈ l) (q : ∀ w, R w → Q w h) : Ok (S.eCell c n) h Q := by
  obtain ⟨w, e, p⟩ := (o _ hx).cell; exact Ok.eCell e (q w p)

/-- `local x = …`: a fresh cell, own from now on -/
theorem Ok.let1 {γ : Type} {k : Nat → List Val → M γ} {vs : List Val} {l : List (Nat × (Val → Prop))}
    {R : Val → Prop} {Q : γ → Heap → Prop} (f : Fresh h) (hs : 16 < h.size) (o : Owns l h) (p : R (vs.headD .nil))
    (r : ∀ h', h'.size = h.size + 1 → (∀ (a : Nat) (o : Obj), h[a]? = some o → h'[a]? = some o) → Fresh h' →
      Owns ((h.size, R) :: l) h' → Ok (k h.size vs.tail) h' Q) :
    Ok (S.let1 k vs) h Q := by
  unfold S.let1; refine Ok.bind (Ok.alloc ?_)
  refine r _ (by simp) (fun _ _ e => push_keep e) f.push ?_
  intro x hx; simp only [List.mem_cons] at hx
  rcases hx with rfl | hx
  · exact Own.fresh f hs p
  · exact (o x hx).push trivial

theorem Ok.eFalse {n : Nat} {Q : Val → Heap → Prop} (q : Q (.bool false) h) : Ok (S.eFalse n) h Q := by
  unfold S.eFalse; exact Ok.tick fun _ _ => Ok.pure q

theorem Ok.eStr {s : List Char} {n : Nat} {Q : Val → Heap → Prop} (q : Q (.str s) h) : Ok (S.eStr s n) h Q := by
  unfold S.eStr; exact Ok.tick fun _ _ => Ok.pure q

theorem Ok.eSite {s : Site} {e : S.SE} {n : Nat} {Q : Val → Heap → Prop} (r : ∀ n', n = n' + 1 → Ok (e n') h Q) :
    Ok (S.eSite s e n) h Q := by unfold S.eSite; exact Ok.tick fun n' hn => Ok.atSite (r n' hn)

theorem Ok.eOr {a b : S.SE} {n : Nat} {Q : Val → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (a n') h fun x h1 => if x.truthy then Q x h1 else Ok (b n') h1 Q) : Ok (S.eOr a b n) h Q := by
  unfold S.eOr; refine Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun x h1 q => ?_)
  split <;> simp_all <;> exact Ok.pure q

theorem Ok.eNot {I : Sem} {a : S.SE} {n : Nat} {Q : Val → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (a n') h fun x h1 => Q (.bool !x.truthy) h1) : Ok (S.eUn I .not a n) h Q := by
  unfold S.eUn; refine Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun x h1 q => ?_)
  rw [unop]; exact Ok.pure q

/-- a field of a table with no metatable, by a string: no call -/
theorem Ok.index_plain {I : Sem} {n a : Nat} {t : Tbl} {s : List Char} {Q : Val → Heap → Prop}
    (ha : h[a]? = some (.tbl t)) (hm : t.mt = none) (q : ∀ v, Q v h) :
    Ok (index I.srcs I.oracle I.tgt n (.tbl a) (.str s)) h Q := by
  cases n with
  | zero => unfold Ok; rw [index]; rfl
  | succ n =>
    unfold Ok; rw [index]
    cases hv : t.get (.str s) <;>
    simp [noDump, Val.isDump, getTbl, getObj, held, weakOf, hm, ha, hv, Val.isNil, Bind.bind, EStateM.bind,
      MonadState.get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure, q]

theorem Ok.eIndex {I : Sem} {t k : S.SE} {n : Nat} {Q : Val → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (t n') h fun tv h1 => Ok (k n') h1 fun kv h2 => Ok (index I.srcs I.oracle I.tgt n' tv kv) h2 Q) :
    Ok (S.eIndex I t k n) h Q := by
  unfold S.eIndex; exact Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun _ _ r1 => Ok.bind r1)

theorem Ok.lNil {n : Nat} {Q : List Val → Heap → Prop} (q : Q [] h) : Ok (S.lNil n) h Q := by
  unfold S.lNil; exact Ok.tick fun _ _ => Ok.pure q

theorem Ok.pNil {n : Nat} {Q : List W → Heap → Prop} (q : Q [] h) : Ok (S.pNil n) h Q := by
  unfold S.pNil; exact Ok.tick fun _ _ => Ok.pure q

theorem Ok.pVar {w : W} {ps : S.SP} {n : Nat} {Q : List W → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (ps n') h fun ws h1 => Q (w :: ws) h1) : Ok (S.pVar w ps n) h Q := by
  unfold S.pVar; exact Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun _ _ q => Ok.pure q)

/-- writes of cells of `l` whose predicates hold of every value -/
theorem Ok.assignCells {l : List (Nat × (Val → Prop))} (n : Nat) (ws : List W) (vs : List Val) (h : Heap)
    (hw : ∀ w ∈ ws, ∃ a, w = S.wCell a ∧ ∀ x ∈ l, x.1 = a → ∀ v, x.2 v) (o : Owns l h) :
    Ok (Lua.assignW n ws vs) h fun _ h' => Owns l h' := by
  induction n generalizing ws vs h with
  | zero => unfold Ok; rw [Lua.assignW]; rfl
  | succ n ih =>
    cases ws with
    | nil => rw [Lua.assignW]; exact Ok.pure o
    | cons w ws =>
      rw [Lua.assignW]
      obtain ⟨a, rfl, pa⟩ := hw w (by simp)
      refine Ok.bind ?_
      unfold Ok; simp only [S.wCell, writeCell, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
      have := ih ws vs.tail _ (fun w hw' => hw w (by simp [hw'])) (o.write (v := vs.headD .nil) fun x hx e => pa x hx e _)
      unfold Ok at this; exact this

theorem Ok.sAssign {ps : S.SP} {es : S.SM} {n : Nat} {Q : Flow → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (ps n') h fun ws h1 => Ok (es n') h1 fun vs h2 =>
      Ok (Lua.assignW n' ws.reverse (vs ++ List.replicate ws.length Val.nil |>.take ws.length).reverse) h2
        fun _ h3 => Q .norm h3) : Ok (S.sAssign ps es n) h Q := by
  unfold S.sAssign
  exact Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun _ _ r1 => Ok.bind (Ok.mono r1 fun _ _ r2 =>
    Ok.bind (Ok.mono r2 fun _ _ q => Ok.pure q)))

theorem Ok.sCall {m : S.SM} {n : Nat} {Q : Flow → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (m n') h fun _ h1 => Q .norm h1) : Ok (S.sCall m n) h Q := by
  unfold S.sCall; exact Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun _ _ q => Ok.pure q)

theorem Ok.sIf {c : S.SE} {t e : S.SB} {n : Nat} {Q : Flow → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (c n') h fun x h1 => if x.truthy then Ok (t n') h1 Q else Ok (e n') h1 Q) :
    Ok (S.sIf c t e n) h Q := by
  unfold S.sIf; refine Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun x h1 q => ?_)
  split <;> simp_all

theorem Ok.qEnd {n : Nat} {Q : Flow → Heap → Prop} (q : Q .norm h) : Ok (S.qEnd n) h Q := by
  unfold S.qEnd; exact Ok.tick fun _ _ => Ok.pure q

theorem Ok.qEndRpt {c : S.SE} {n : Nat} {Q : Flow → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (c n') h fun _ h1 => Q .norm h1 ∧ Q .brk h1) : Ok (S.qEndRpt c n) h Q := by
  unfold S.qEndRpt; refine Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) fun x h1 q => Ok.pure ?_)
  split
  · exact q.2
  · exact q.1

/-- a statement that ends normally, then the rest -/
theorem Ok.qStat {s : S.SB} {g : String → M Flow} {q : S.SB} {n : Nat} {Q : Flow → Heap → Prop}
    (r : ∀ n', n = n' + 1 → Ok (s n') h fun fl h1 => fl = .norm ∧ Ok (q n') h1 Q) : Ok (S.qStat s g q n) h Q := by
  unfold S.qStat
  refine Ok.tick fun n' hn => Ok.bind (Ok.mono (r n' hn) ?_)
  rintro _ _ ⟨rfl, q⟩; exact q

/-- `repeat … until`: a body that keeps `Inv` and ends normally or by the condition -/
theorem Ok.rptL {b : S.SB} {Inv : Heap → Prop}
    (hb : ∀ n h, Inv h → Ok (b n) h fun fl h' => (fl = .norm ∨ fl = .brk) ∧ Inv h') :
    ∀ n h, Inv h → Ok (S.rptL b n) h fun fl h' => fl = .norm ∧ Inv h' := by
  intro n; induction n with
  | zero => intro h _; unfold Ok; rw [S.rptL]; rfl
  | succ n ih =>
    intro h i; rw [S.rptL]
    refine Ok.bind (Ok.mono (hb n h i) ?_)
    rintro _ h1 ⟨rfl | rfl, i1⟩
    · exact ih h1 i1
    · exact Ok.pure ⟨rfl, i1⟩

theorem Ok.sRepeat {b : S.SB} {Inv : Heap → Prop} {n : Nat} (i : Inv h)
    (hb : ∀ n h, Inv h → Ok (b n) h fun fl h' => (fl = .norm ∨ fl = .brk) ∧ Inv h') :
    Ok (S.sRepeat b n) h fun fl h' => fl = .norm ∧ Inv h' := by
  unfold S.sRepeat; exact Ok.tick fun n' _ => Ok.rptL hb n' h i

/-- a call of the builtin `pcall`, as a call site makes it: no Lua error, and every own cell kept -/
theorem Ok.pcallOwns {I : Sem} {n : Nat} {fn0 : Nat} {f : Val} {as : List Val} {l : List (Nat × (Val → Prop))}
    (o : Owns l h) :
    Ok (fenvCall (some fn0) (.prim "pcall" []) (f :: as) (call I.srcs I.oracle I.tgt n (.prim "pcall" []) (f :: as))) h
      fun _ h' => Owns l h' := by
  simp only [fenvCall]
  exact Ok.mono (Ok.keeps (Ok.pcall I n f as) (fun _ _ => call_keeps) o) fun _ _ x => x.2

end rules

/-- what R2 rests on holds as the semantics starts: `_G` has no metatable and its `pcall` is the builtin -/
theorem pcall_init : ∃ g, initHeap[G]? = some (.tbl g) ∧ g.mt = none ∧ g.get (lstr "pcall") = .prim "pcall" [] :=
  ⟨_, rfl, rfl, rfl⟩

/-- a cell of an `Owns` list -/
macro "mem" : tactic => `(tactic| repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem))
/-- writes of cells whose predicates hold of every value: cells other than those with a value of their own -/
macro "wcells" : tactic => `(tactic| (simp; repeat' (first | (intro _; omega) | exact ⟨_, rfl, ?_⟩ | constructor)))
/-- an object of the heap before some allocations -/
macro "kept" : tactic => `(tactic| solve_by_elim (maxDepth := 20))

/-- the closure `M.loop` is: watchd.lua's, its upvalue `iteration` at cell `c_it` -/
def loopClo (env0 : Env) (fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat) (root0 : Option Nat) (ks0 : List (Nat × Nat)) : Clo :=
  ⟨["c", "mine", "comms", "repo", "opts"], false, M_loop_body, env0, fenv0, src0, ln0, root0, ks0⟩

/-- R2: a call of `M.loop` ends in no Lua error, for every oracle, every fuel, every other argument, and every value
`iteration` holds, whatever it does when called. What it rests on: `pcall` is the builtin, a field of the function's
environment (`_G`, which has no metatable); `opts` is a table with no metatable (cmd_watchd's literal), read before
any call; the heap is `Fresh` (no coroutine holds a heap), so the loop's locals are own for good. An iteration may
leave suspended coroutines, so `Fresh` need not hold after it: that is why each iteration runs under the loop's own
`pcall`, and why `iteration_safe` does not stand in for that pcall. -/
theorem loop_safe (I : Sem) (env0 : Env) (fn0 fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat)
    (root0 : Option Nat) (ks0 : List (Nat × Nat)) (c_it : Nat)
    (h_it : env0.lookup "iteration" = some c_it) (h_pcall : env0.lookup "pcall" = none)
    (h : Heap) (hfn : h[fn0]? = some (.clo (loopClo env0 fenv0 src0 ln0 root0 ks0)))
    (v : Val) (hv : h[c_it]? = some (.cell v))
    (g : Tbl) (hg : h[fenv0]? = some (.tbl g)) (hgm : g.mt = none) (hp : g.get (lstr "pcall") = .prim "pcall" [])
    (hf : Fresh h) (hs : 16 < h.size)
    (args : List Val) (ao : Nat) (o : Tbl) (hopts : args[4]? = some (.tbl ao)) (hao : h[ao]? = some (.tbl o))
    (hom : o.mt = none) (n : Nat) :
    Ok (call I.srcs I.oracle I.tgt n (.fn fn0) args) h fun _ _ => True := by
  obtain ⟨a0, a1, a2, a3, rest, rfl⟩ : ∃ a0 a1 a2 a3 rest, args = a0 :: a1 :: a2 :: a3 :: .tbl ao :: rest := by
    match args, hopts with
    | a0 :: a1 :: a2 :: a3 :: _ :: rest, e => simp at e; exact ⟨a0, a1, a2, a3, rest, by rw [e]⟩
  cases n with
  | zero => unfold Ok; rw [call]; rfl
  | succ n =>
  refine Ok.congr (call_fn I n fn0 _ h _ hfn) ?_
  rw [loopClo, ← M_loop_ok I env0 fn0 fenv0 src0 ln0 root0 ks0 c_it h_it h_pcall _ n]
  unfold M_loop S.fn
  refine Ok.frame (Ok.onFrames (Ok.bind (Ok.mono (P := fun fl _ => ∃ vs, fl = .ret vs) ?_ ?_)))
  rotate_left
  · rintro _ _ ⟨vs, rfl⟩; exact Ok.pure trivial
  -- the parameters
  refine Ok.let1 (R := fun _ => True) hf hs (l := []) (fun _ h => by simp at h) trivial fun h1 s1 k1 f1 o1 => ?_
  refine Ok.let1 (R := fun _ => True) f1 (by omega) o1 trivial fun h2 s2 k2 f2 o2 => ?_
  refine Ok.let1 (R := fun _ => True) f2 (by omega) o2 trivial fun h3 s3 k3 f3 o3 => ?_
  refine Ok.let1 (R := fun _ => True) f3 (by omega) o3 trivial fun h4 s4 k4 f4 o4 => ?_
  refine Ok.let1 (R := (· = .tbl ao)) f4 (by omega) o4 rfl fun h5 s5 k5 f5 o5 => ?_
  -- local pcall, iteration, once = pcall, iteration, opts.once: no call
  refine Ok.block fun n _ => Ok.qLocal fun n _ => ?_
  refine Ok.lCons fun n _ => Ok.eGlob_pcall (c := loopClo env0 fenv0 src0 ln0 root0 ks0) (by kept) (by simp only [loopClo]; kept) hgm hp ?_
  refine Ok.lCons fun n _ => Ok.eCell (by kept) ?_
  refine Ok.lLast fun n _ => Ok.mSite fun n _ => Ok.mOne fun n _ => Ok.eIndex fun n _ => ?_
  refine Ok.eCellOwn o5 (by mem) fun w e => ?_
  subst e
  refine Ok.eStr (Ok.index_plain (by kept) hom fun x => ?_)
  refine Ok.let1 (R := (· = .prim "pcall" [])) f5 (by omega) o5 rfl fun h6 s6 k6 f6 o6 => ?_
  refine Ok.let1 (R := fun _ => True) f6 (by omega) o6 trivial fun h7 s7 k7 f7 o7 => ?_
  refine Ok.let1 (R := fun _ => True) f7 (by omega) o7 trivial fun h8 s8 k8 f8 o8 => ?_
  -- local up, ok, r, why = false
  refine Ok.qLocal fun n _ => Ok.lLast fun n _ => Ok.mOne fun n _ => Ok.eFalse ?_
  refine Ok.let1 (R := fun _ => True) f8 (by omega) o8 trivial fun h9 s9 k9 f9 o9 => ?_
  refine Ok.let1 (R := fun _ => True) f9 (by omega) o9 trivial fun h10 s10 k10 f10 o10 => ?_
  refine Ok.let1 (R := fun _ => True) f10 (by omega) o10 trivial fun h11 s11 k11 f11 o11 => ?_
  refine Ok.let1 (R := fun _ => True) f11 (by omega) o11 trivial fun h12 s12 k12 f12 o12 => ?_
  -- the loop: each iteration under pcall, every own cell kept
  refine Ok.qStat fun n _ => Ok.mono (Ok.sRepeat (Inv := Owns _) o12 ?_) fun fl h' ⟨e, o'⟩ => ⟨e, ?_⟩
  · intro n h' o'
    refine Ok.qStat fun n _ => Ok.sAssign fun n _ => Ok.pVar fun n _ => Ok.pVar fun n _ => Ok.pVar fun n _ =>
      Ok.pNil ?_
    refine Ok.lLast fun n _ => Ok.mSite fun n _ => Ok.mCall fun n _ => Ok.eCellOwn o' (by mem) fun w e => ?_
    subst e
    refine Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.lLast fun n _ => Ok.mOne fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.mono (Ok.pcallOwns o') fun _ h2 o2 => Ok.mono (Ok.assignCells _ _ _ _ ?_ o2) fun _ h3 o3 => ⟨rfl, ?_⟩
    · wcells
    -- up = ok and r
    refine Ok.qStat fun n _ => Ok.sAssign fun n _ => Ok.pVar fun n _ => Ok.pNil ?_
    refine Ok.lLast fun n _ => Ok.mOne fun n _ => Ok.eAnd fun n _ => Ok.eCellOwn o3 (by mem) fun w _ => ?_
    split
    case' isTrue => refine Ok.eCellOwn o3 (by mem) fun _ _ => ?_
    all_goals
      refine Ok.mono (Ok.assignCells _ _ _ _ (by wcells) o3) fun _ h4 o4 => ⟨rfl, ?_⟩
      refine Ok.qEndRpt fun n _ => Ok.eOr fun n _ => Ok.eCellOwn o4 (by mem) fun w _ => ?_
      split
      · exact ⟨⟨Or.inl rfl, o4⟩, ⟨Or.inr rfl, o4⟩⟩
      · exact Ok.eCellOwn o4 (by mem) fun _ _ => ⟨⟨Or.inl rfl, o4⟩, ⟨Or.inr rfl, o4⟩⟩
  · refine Ok.qStat_ret fun n _ => Ok.sReturn fun n _ => Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    exact Ok.lLast fun n _ => Ok.mOne fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => trivial

set_option hygiene false in
/-- iteration's lines after its first if: `if not why and not once then pcall(pause, interval) end; return up, why` -/
local macro "rest" : tactic => `(tactic| (
  refine Ok.qStat fun n _ => Ok.sIf fun n _ => Ok.eAnd fun n _ => Ok.eNot fun n _ => Ok.eCellOwn o' (by mem) fun w _ => ?_
  split
  case' isTrue => refine Ok.eNot fun n _ => Ok.eCellOwn o' (by mem) fun w _ => ?_
  all_goals try split
  all_goals first
    | (refine Ok.block fun n _ => Ok.qStat fun n _ => Ok.sCall fun n _ => ?_
       refine Ok.mSite fun n _ => Ok.mCall fun n _ => Ok.eCellOwn o' (by mem) fun w e => ?_
       subst e
       refine Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
       refine Ok.lLast fun n _ => Ok.mOne fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
       refine Ok.mono (Ok.pcallOwns o') fun _ h' o' => ⟨rfl, Ok.qEnd ⟨rfl, ?_⟩⟩)
    | refine Ok.block fun n _ => Ok.qEnd ⟨rfl, ?_⟩
  all_goals
    refine Ok.qStat_ret fun n _ => Ok.sReturn fun n _ => Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    exact Ok.lLast fun n _ => Ok.mOne fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => trivial))

/-- the closure `iteration` is: watchd.lua's -/
def itClo (env0 : Env) (fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat) (root0 : Option Nat) (ks0 : List (Nat × Nat)) : Clo :=
  ⟨["c", "mine", "comms", "repo", "opts", "up"], false, iteration_body, env0, fenv0, src0, ln0, root0, ks0⟩

/-- R2 of `iteration`: its three pcalls and the lines between them end in no Lua error, whatever the pass, the
report and the pause do. What it rests on: `pcall` as for `loop_safe`, `M` and `opts` tables with no metatable (both
read before any call), and a `Fresh` heap. -/
theorem iteration_safe (I : Sem) (env0 : Env) (fn0 fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat)
    (root0 : Option Nat) (ks0 : List (Nat × Nat)) (c_M c_pause : Nat)
    (h_M : env0.lookup "M" = some c_M) (h_pause : env0.lookup "pause" = some c_pause)
    (h_pcall : env0.lookup "pcall" = none)
    (h : Heap) (hfn : h[fn0]? = some (.clo (itClo env0 fenv0 src0 ln0 root0 ks0)))
    (aM : Nat) (tM : Tbl) (hM : h[c_M]? = some (.cell (.tbl aM))) (haM : h[aM]? = some (.tbl tM)) (hMm : tM.mt = none)
    (vp : Val) (hvp : h[c_pause]? = some (.cell vp))
    (g : Tbl) (hg : h[fenv0]? = some (.tbl g)) (hgm : g.mt = none) (hp : g.get (lstr "pcall") = .prim "pcall" [])
    (hf : Fresh h) (hs : 16 < h.size)
    (args : List Val) (ao : Nat) (o : Tbl) (hopts : args[4]? = some (.tbl ao)) (hao : h[ao]? = some (.tbl o))
    (hom : o.mt = none) (n : Nat) :
    Ok (call I.srcs I.oracle I.tgt n (.fn fn0) args) h fun _ _ => True := by
  obtain ⟨a0, a1, a2, a3, rest, rfl⟩ : ∃ a0 a1 a2 a3 rest, args = a0 :: a1 :: a2 :: a3 :: .tbl ao :: rest := by
    match args, hopts with
    | a0 :: a1 :: a2 :: a3 :: _ :: rest, e => simp at e; exact ⟨a0, a1, a2, a3, rest, by rw [e]⟩
  cases n with
  | zero => unfold Ok; rw [call]; rfl
  | succ n =>
  refine Ok.congr (call_fn I n fn0 _ h _ hfn) ?_
  rw [itClo, ← iteration_ok I env0 fn0 fenv0 src0 ln0 root0 ks0 c_M c_pause h_M h_pause h_pcall _ n]
  unfold iteration S.fn
  refine Ok.frame (Ok.onFrames (Ok.bind (Ok.mono (P := fun fl _ => ∃ vs, fl = .ret vs) ?_ ?_)))
  rotate_left
  · rintro _ _ ⟨vs, rfl⟩; exact Ok.pure trivial
  -- the parameters
  refine Ok.let1 (R := fun _ => True) hf hs (l := []) (fun _ h => by simp at h) trivial fun h1 s1 k1 f1 o1 => ?_
  refine Ok.let1 (R := fun _ => True) f1 (by omega) o1 trivial fun h2 s2 k2 f2 o2 => ?_
  refine Ok.let1 (R := fun _ => True) f2 (by omega) o2 trivial fun h3 s3 k3 f3 o3 => ?_
  refine Ok.let1 (R := fun _ => True) f3 (by omega) o3 trivial fun h4 s4 k4 f4 o4 => ?_
  refine Ok.let1 (R := (· = .tbl ao)) f4 (by omega) o4 rfl fun h5 s5 k5 f5 o5 => ?_
  refine Ok.let1 (R := fun _ => True) f5 (by omega) o5 trivial fun h6 s6 k6 f6 o6 => ?_
  -- local pcall, pass, failed, pause, once, interval = pcall, M.watchd_pass, M.tick_failed, pause, opts.once,
  -- opts.interval: no call
  refine Ok.block fun n _ => Ok.qLocal fun n _ => ?_
  refine Ok.lCons fun n _ => Ok.eGlob_pcall (c := itClo env0 fenv0 src0 ln0 root0 ks0) (by kept) (by simp only [itClo]; kept) hgm hp ?_
  refine Ok.lCons fun n _ => Ok.eSite fun n _ => Ok.eIndex fun n _ => Ok.eCell (by kept) ?_
  refine Ok.eStr (Ok.index_plain (by kept) hMm fun x1 => ?_)
  refine Ok.lCons fun n _ => Ok.eSite fun n _ => Ok.eIndex fun n _ => Ok.eCell (by kept) ?_
  refine Ok.eStr (Ok.index_plain (by kept) hMm fun x2 => ?_)
  refine Ok.lCons fun n _ => Ok.eCell (by kept) ?_
  refine Ok.lCons fun n _ => Ok.eSite fun n _ => Ok.eIndex fun n _ => Ok.eCellOwn o6 (by mem) fun w e => ?_
  subst e
  refine Ok.eStr (Ok.index_plain (by kept) hom fun x3 => ?_)
  refine Ok.lLast fun n _ => Ok.mSite fun n _ => Ok.mOne fun n _ => Ok.eIndex fun n _ => Ok.eCellOwn o6 (by mem) fun w e => ?_
  subst e
  refine Ok.eStr (Ok.index_plain (by kept) hom fun x4 => ?_)
  refine Ok.let1 (R := (· = .prim "pcall" [])) f6 (by omega) o6 rfl fun h7 s7 k7 f7 o7 => ?_
  refine Ok.let1 (R := fun _ => True) f7 (by omega) o7 trivial fun h8 s8 k8 f8 o8 => ?_
  refine Ok.let1 (R := fun _ => True) f8 (by omega) o8 trivial fun h9 s9 k9 f9 o9 => ?_
  refine Ok.let1 (R := fun _ => True) f9 (by omega) o9 trivial fun h10 s10 k10 f10 o10 => ?_
  refine Ok.let1 (R := fun _ => True) f10 (by omega) o10 trivial fun h11 s11 k11 f11 o11 => ?_
  refine Ok.let1 (R := fun _ => True) f11 (by omega) o11 trivial fun h12 s12 k12 f12 o12 => ?_
  -- local ok, r, why
  refine Ok.qLocal fun n _ => Ok.lNil ?_
  refine Ok.let1 (R := fun _ => True) f12 (by omega) o12 trivial fun h13 s13 k13 f13 o13 => ?_
  refine Ok.let1 (R := fun _ => True) f13 (by omega) o13 trivial fun h14 s14 k14 f14 o14 => ?_
  refine Ok.let1 (R := fun _ => True) f14 (by omega) o14 trivial fun h15 s15 k15 f15 o15 => ?_
  -- ok, r, why = pcall(pass, c, mine, comms, repo, opts, up)
  refine Ok.qStat fun n _ => Ok.sAssign fun n _ => Ok.pVar fun n _ => Ok.pVar fun n _ => Ok.pVar fun n _ =>
    Ok.pNil ?_
  refine Ok.lLast fun n _ => Ok.mSite fun n _ => Ok.mCall fun n _ => Ok.eCellOwn o15 (by mem) fun w e => ?_
  subst e
  refine Ok.lCons fun n _ => Ok.eCellOwn o15 (by mem) fun _ _ => ?_
  refine Ok.lCons fun n _ => Ok.eCellOwn o15 (by mem) fun _ _ => ?_
  refine Ok.lCons fun n _ => Ok.eCellOwn o15 (by mem) fun _ _ => ?_
  refine Ok.lCons fun n _ => Ok.eCellOwn o15 (by mem) fun _ _ => ?_
  refine Ok.lCons fun n _ => Ok.eCellOwn o15 (by mem) fun _ _ => ?_
  refine Ok.lCons fun n _ => Ok.eCellOwn o15 (by mem) fun _ _ => ?_
  refine Ok.lLast fun n _ => Ok.mOne fun n _ => Ok.eCellOwn o15 (by mem) fun _ _ => ?_
  refine Ok.mono (Ok.pcallOwns o15) fun _ h' o' => Ok.mono (Ok.assignCells _ _ _ _ (by wcells) o') fun _ h' o' => ⟨rfl, ?_⟩
  -- if ok then up = r else pcall(failed, c, comms, r) end
  refine Ok.qStat fun n _ => Ok.sIf fun n _ => Ok.eCellOwn o' (by mem) fun w _ => ?_
  split
  · refine Ok.block fun n _ => Ok.qStat fun n _ => Ok.sAssign fun n _ => Ok.pVar fun n _ => Ok.pNil ?_
    refine Ok.lLast fun n _ => Ok.mOne fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.mono (Ok.assignCells _ _ _ _ (by wcells) o') fun _ h' o' => ⟨rfl, Ok.qEnd ⟨rfl, ?_⟩⟩
    rest
  · refine Ok.block fun n _ => Ok.qStat fun n _ => Ok.sCall fun n _ => ?_
    refine Ok.mSite fun n _ => Ok.mCall fun n _ => Ok.eCellOwn o' (by mem) fun w e => ?_
    subst e
    refine Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.lCons fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.lLast fun n _ => Ok.mOne fun n _ => Ok.eCellOwn o' (by mem) fun _ _ => ?_
    refine Ok.mono (Ok.pcallOwns o') fun _ h' o' => ⟨rfl, Ok.qEnd ⟨rfl, ?_⟩⟩
    rest

end Swarm.LoopSafe
