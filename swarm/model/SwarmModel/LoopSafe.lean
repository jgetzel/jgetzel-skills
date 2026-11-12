import SwarmModel.Lifted.Watchd
import LuaLean.Hoare

/-! W1 (board #67): no Lua error escapes an iteration of watchd's loop, on the real Lua. `M.iterate`
(swarm/lua/swarm/watchd.lua, lifted: `Lifted/Watchd.lean`) is one iteration: it calls `iteration`, which runs the pass,
an error's report and the pause, under `pcall`. Every external call iteration makes (hc, git, sqlite, re, io) is in
it, so here it is arbitrary: any value, which when called may return anything, raise anything, change the heap in
any way and call any effect, and the oracle is any oracle. -/

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

theorem push_top {x : Obj} : (h.push x)[h.size]? = some x := by simp

/-- a cell or object of the heap before some allocations -/
macro "cell" : tactic => `(tactic| repeat (first | exact push_top | assumption | apply push_keep))

/-! The shallow combinators `M.iterate` is made of (`LuaLean/Shallow.lean`) -/

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

end rules

/-- the closure `M.iterate` is: watchd.lua's, its upvalue `iteration` at cell `c_it` -/
def iterClo (env0 : Env) (fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat) : Clo :=
  ⟨["c", "mine", "comms", "repo", "opts", "up"], false, M_iterate_body, env0, fenv0, src0, ln0⟩

/-- what W1 rests on holds as the semantics starts: `_G` has no metatable and its `pcall` is the builtin -/
theorem pcall_init : ∃ g, initHeap[G]? = some (.tbl g) ∧ g.mt = none ∧ g.get (lstr "pcall") = .prim "pcall" [] :=
  ⟨_, rfl, rfl, rfl⟩

/-- W1: a call of `M.iterate` ends in no Lua error, for every oracle, every fuel, every argument, and every value
`iteration` holds, whatever it does when called. What it rests on: `pcall` is the builtin, a field of the function's
environment (`_G`, which has no metatable). -/
theorem iterate_safe (I : Sem) (env0 : Env) (fn0 fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat) (c_it : Nat)
    (h_it : env0.lookup "iteration" = some c_it) (h_pcall : env0.lookup "pcall" = none)
    (h : Heap) (hfn : h[fn0]? = some (.clo (iterClo env0 fenv0 src0 ln0)))
    (v : Val) (hv : h[c_it]? = some (.cell v))
    (g : Tbl) (hg : h[fenv0]? = some (.tbl g)) (hgm : g.mt = none) (hp : g.get (lstr "pcall") = .prim "pcall" [])
    (args : List Val) (n : Nat) :
    Ok (call I.srcs I.oracle I.tgt n (.fn fn0) args) h fun _ _ => True := by
  cases n with
  | zero => unfold Ok; rw [call]; rfl
  | succ n =>
  refine Ok.congr (call_fn I n fn0 args h _ hfn) ?_
  rw [iterClo, ← M_iterate_ok I env0 fn0 fenv0 src0 ln0 c_it h_it h_pcall args n]
  unfold M_iterate S.fn
  refine Ok.frame (Ok.onFrames (Ok.bind (Ok.mono (P := fun fl _ => ∃ vs, fl = .ret vs) ?_ ?_)))
  rotate_left
  · rintro _ _ ⟨vs, rfl⟩; exact Ok.pure trivial
  simp only [S.let1, S.letEnd]
  refine Ok.bind (Ok.alloc ?_)
  refine Ok.bind (Ok.alloc ?_)
  refine Ok.bind (Ok.alloc ?_)
  refine Ok.bind (Ok.alloc ?_)
  refine Ok.bind (Ok.alloc ?_)
  refine Ok.bind (Ok.alloc ?_)
  refine Ok.block fun n _ => ?_
  refine Ok.qLocal fun n _ => Ok.mono (P := fun _ _ => True) ?_ fun vs h1 _ => ?_
  · -- the pcall of iteration
    refine Ok.lLast fun n _ => Ok.mSite fun n _ => Ok.mCall fun n _ => ?_
    refine Ok.eGlob_pcall (c := iterClo env0 fenv0 src0 ln0) ?_ ?_ hgm hp ?_
    · cell
    · simp only [iterClo]; cell
    refine Ok.lCons fun n _ => Ok.eCell (by cell) ?_
    refine Ok.lCons fun n _ => Ok.eCell (by cell) ?_
    refine Ok.lCons fun n _ => Ok.eCell (by cell) ?_
    refine Ok.lCons fun n _ => Ok.eCell (by cell) ?_
    refine Ok.lCons fun n _ => Ok.eCell (by cell) ?_
    refine Ok.lCons fun n _ => Ok.eCell (by cell) ?_
    refine Ok.lLast fun n _ => Ok.mOne fun n _ => Ok.eCell (by cell) ?_
    exact Ok.pcall I _ _ _
  · -- ok, r, why: fresh cells of the heap pcall returns, whatever it is
    simp only [S.let1, S.letEnd]
    refine Ok.bind (Ok.alloc (Ok.bind (Ok.alloc (Ok.bind (Ok.alloc ?_)))))
    refine Ok.qStat_ret fun n _ => Ok.sReturn fun n _ => ?_
    refine Ok.lCons fun n _ => Ok.eAnd fun n _ => Ok.eCell (by cell) ?_
    split
    · exact Ok.eCell (by cell) (Ok.lLast fun n _ => Ok.mOne fun n _ =>
        Ok.eCell (by cell) trivial)
    · exact Ok.lLast fun n _ => Ok.mOne fun n _ => Ok.eCell (by cell) trivial

end Swarm.LoopSafe
