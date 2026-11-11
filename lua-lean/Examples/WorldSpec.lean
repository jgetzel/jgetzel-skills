import Examples.World
import LuaLean.Hoare

/-! Specs of `test/world.lua` (lifted: `Examples/World.lean`) under named axioms about the world it runs in
(DESIGN.md, *Effects*): what `greet` and `readings` add to the trace of effects. The axioms are about `real`, the
world of the machine the script runs on; each is tested against LuaJIT there by the case of its name in
`world_axioms.lua`, and `consistent` shows a world that has them all, so together they cannot prove `False`. -/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace World
open Lua

/-! ## The world -/

/-- the world the script runs in -/
opaque real : Oracle

/-- the world takes a write to the default output: io.write gets an answer -/
def TakesWrites (o : Oracle) : Prop := ∀ s l, ∃ vs, o "io.write" [.str s] l = some vs
/-- the clock answers a time_t -/
def ClockAnswers (o : Oracle) : Prop := ∀ l, ∃ t : Int, o "os.time" [] l = some [.num (.int t)]
/-- the clock never goes back: an answer is no earlier than one before it (NTP stepping the clock back breaks it) -/
def ClockMono (o : Oracle) : Prop :=
  ∀ l t t', o "os.time" [] l = some [.num (.int t)] → ⟨"os.time", [], [.num (.int t')]⟩ ∈ l → t' ≤ t

/-- io.write (world_axioms: takes_writes) -/
axiom takes_writes : TakesWrites real
/-- os.time() (world_axioms: clock_answers) -/
axiom clock_answers : ClockAnswers real
/-- os.time() twice (world_axioms: clock_mono) -/
axiom clock_mono : ClockMono real

def timeOf : Event → Option Int
  | ⟨"os.time", [], [.num (.int t)]⟩ => some t
  | _ => none

/-- the latest time the clock gave in a trace, 0 before the first -/
def latest (l : List Event) : Int := l.foldr (fun e m => match timeOf e with | some t => max t m | none => m) 0

theorem latest_ge (t : Int) : ∀ l : List Event, ⟨"os.time", [], [.num (.int t)]⟩ ∈ l → t ≤ latest l
  | [], h => nomatch h
  | e :: l, h => by
    have ih := latest_ge t l
    simp only [latest, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · exact Int.le_max_left _ _
    · split
      · exact Int.le_trans (ih h) (Int.le_max_right _ _)
      · exact ih h

/-- a world with every assumption: stdout takes every write, and the clock stands still -/
def ideal : Oracle := fun name args l => match name, args with
  | "io.write", _ => some [.bool true]
  | "os.time", [] => some [.num (.int (latest l))]
  | _, _ => none

theorem consistent : TakesWrites ideal ∧ ClockAnswers ideal ∧ ClockMono ideal :=
  ⟨fun _ _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩, fun l t t' e m => by
    simp only [ideal, Option.some.injEq, List.cons.injEq, Val.num.injEq, Num.int.injEq, and_true] at e
    exact e ▸ latest_ge t' l m⟩

/-! ## The script -/

/-- the heap has io.write and os.time where the script reads them, and the trace -/
structure Lib (h : Heap) : Prop where
  log : ∃ l, h[LOG]? = some (.log l)
  g : ∃ gt, h[G]? = some (.tbl gt) ∧ ∃ io os, gt.get (lstr "io") = .tbl io ∧ gt.get (lstr "os") = .tbl os ∧
    (∃ t, h[io]? = some (.tbl t) ∧ t.get (lstr "write") = .prim "io.write" [] ∧ t.mt = none) ∧
    (∃ t, h[os]? = some (.tbl t) ∧ t.get (lstr "time") = .prim "os.time" [] ∧ t.mt = none)

/-- as the semantics starts -/
theorem lib_init : Lib initHeap :=
  ⟨⟨_, rfl⟩, _, rfl, 9, 10, rfl, rfl, ⟨_, rfl, rfl, rfl⟩, ⟨_, rfl, rfl, rfl⟩⟩

theorem lt_of_some {h : Heap} {a : Nat} {o : Obj} (e : h[a]? = some o) : a < h.size := by
  rcases Nat.lt_or_ge a h.size with h1 | h1
  · exact h1
  · simp [Array.getElem?_eq_none h1] at e

theorem get_of_some {h : Heap} {a : Nat} {o : Obj} (e : h[a]? = some o) : h[a]'(lt_of_some e) = o := by
  rw [Array.getElem?_eq_getElem (lt_of_some e)] at e; exact Option.some.inj e

theorem greet_run (I : Sem) (env0 : Env) (h : Heap) (L : Lib h) (s : List Char) (vs : List Val)
    (hw : I.oracle "io.write" [.str ("hello, ".toList ++ s ++ "\n".toList)] (trace h) = some vs) (n : Nat) :
    greet I env0 [.str s] (n + 20) h = .ok [] ((h.push (.cell (.str s))).setIfInBounds LOG
      (.log (⟨"io.write", [.str ("hello, ".toList ++ s ++ "\n".toList)], vs⟩ :: trace h))) := by
  obtain ⟨⟨l, hl⟩, gt, hg, io, os, hio, hos, ⟨t, ht, htw, htm⟩, -⟩ := L
  have hs6 := lt_of_some hl
  have hG := lt_of_some hg
  have hI := lt_of_some ht
  have hg' := get_of_some hg
  have ht' := get_of_some ht
  simp [lstr] at hio htw hos hw
  simp only [greet, S.fn, S.let1, S.letEnd, S.block, S.qStat, S.sCall, S.mSite, S.mCall, S.eSite, S.eIndex, S.eGlob,
    S.eStr, S.lCons, S.lLast, S.mOne, S.eCell, S.qEnd, tick]
  simp [lstr, rawget, getTbl, getObj, readCell, bind, EStateM.bind, pure, EStateM.pure, alloc, get, set, getThe,
    MonadStateOf.get, MonadStateOf.set, EStateM.get, EStateM.set, frame, atSite, Array.getElem?_push, hG, hg', hio,
    Nat.ne_of_lt hG]
  rw [index.eq_def]
  simp [lstr, rawget, getTbl, getObj, readCell, bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, Array.getElem?_push, ht', htw, hI, Nat.ne_of_lt hI, Val.isNil, htm, wget, held, weakOf, noDump, Val.isDump, call_prim, callPrim_write, ioWrite]
  simp [effect, trace_push _ hs6, hw, frame, EStateM.bind, EStateM.pure, atSite, List.findIdx?_cons,
    List.findIdx?_nil]

theorem readings_run (I : Sem) (env0 : Env) (h : Heap) (L : Lib h) (t0 t1 : Int)
    (e0 : I.oracle "os.time" [] (trace h) = some [.num (.int t0)])
    (e1 : I.oracle "os.time" [] (⟨"os.time", [], [.num (.int t0)]⟩ :: trace h) = some [.num (.int t1)]) (n : Nat) :
    readings I env0 [] (n + 30) h = .ok [timeVal t0, timeVal t1]
      ((((h.setIfInBounds LOG (.log (⟨"os.time", [], [.num (.int t0)]⟩ :: trace h))).push
        (.cell (timeVal t0))).setIfInBounds LOG
        (.log (⟨"os.time", [], [.num (.int t1)]⟩ :: ⟨"os.time", [], [.num (.int t0)]⟩ :: trace h))).push
        (.cell (timeVal t1))) := by
  obtain ⟨⟨l, hl⟩, gt, hg, io, os, hio, hos, -, ⟨t, ht, htw, htm⟩⟩ := L
  have hs6 := lt_of_some hl
  have hG := lt_of_some hg
  have hI := lt_of_some ht
  have hg' := get_of_some hg
  have ht' := get_of_some ht
  have hoL : os ≠ LOG := by rintro rfl; simp [ht] at hl
  have hGL : G ≠ LOG := by decide
  have tr1 := trace_set (⟨"os.time", [], [.num (.int t0)]⟩ :: trace h) hs6
  simp [lstr] at hio htw hos
  simp only [readings, S.fn, S.let1, S.letEnd, S.block, S.qStat, S.qLocal, S.sReturn, S.mSite, S.mCall, S.eSite,
    S.eIndex, S.eGlob, S.eStr, S.lCons, S.lLast, S.lNil, S.mOne, S.eCell, S.qEnd, tick]
  simp [lstr, rawget, getTbl, getObj, readCell, bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, Array.getElem?_push, hG, hg', hos, ht', htw, hI, Nat.ne_of_lt hG, Nat.ne_of_lt hI, frame, atSite]
  rw [index.eq_def]
  simp [lstr, rawget, getTbl, getObj, readCell, bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get,
    EStateM.get, Array.getElem?_push, hG, hg', hos, ht', htw, hI, Nat.ne_of_lt hG, Nat.ne_of_lt hI, Val.isNil, htm, wget, held, weakOf, noDump, Val.isDump,
    call_prim, callPrim_time, timeFx, effect, e0, frame, atSite]
  simp [lstr, rawget, getTbl, getObj, readCell, alloc, set, MonadStateOf.set, EStateM.set, bind, EStateM.bind,
    pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, Array.getElem?_push, Array.getElem?_setIfInBounds,
    Array.getElem_setIfInBounds, Array.getElem_push, hG, hg', hI, ht', hos, htw, hs6, hoL, Ne.symm hoL, hGL,
    Ne.symm hGL, Nat.ne_of_lt hG, Nat.ne_of_lt hI, frame, atSite, Val.isNil, htm, wget, held, weakOf, noDump, Val.isDump, call_prim, callPrim_time, timeFx,
    effect, tr1, e1]
  rw [index.eq_def]
  simp [lstr, rawget, getTbl, getObj, readCell, alloc, set, MonadStateOf.set, EStateM.set, bind, EStateM.bind,
    pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, Array.getElem?_push, Array.getElem?_setIfInBounds,
    Array.getElem_setIfInBounds, Array.getElem_push, hG, hg', hI, ht', hos, htw, hs6, hoL, Ne.symm hoL, hGL,
    Ne.symm hGL, Nat.ne_of_lt hG, Nat.ne_of_lt hI, frame, atSite, Val.isNil, htm, wget, held, weakOf, noDump, Val.isDump, call_prim, callPrim_time, timeFx,
    effect, tr1, e1, trace_push, trace_set, Array.size_setIfInBounds, Array.size_push, Nat.ne_of_lt hs6,
    (Nat.ne_of_lt hs6).symm]

/-! ## The specs -/

/-- greet writes its line to the default output, and does nothing else in the world -/
theorem greet_spec (I : Sem) (hI : I.oracle = real) (env0 : Env) (h : Heap) (L : Lib h) (s : List Char) :
    RunP (greet I env0 [.str s]) h fun r h' => r = [] ∧
      ∃ vs, trace h' = ⟨"io.write", [.str ("hello, ".toList ++ s ++ "\n".toList)], vs⟩ :: trace h := by
  obtain ⟨vs, e⟩ := takes_writes ("hello, ".toList ++ s ++ "\n".toList) (trace h)
  rw [← hI] at e
  have hs6 := lt_of_some L.log.choose_spec
  refine ⟨20, [], (h.push (.cell (.str s))).setIfInBounds LOG
    (.log (⟨"io.write", [.str ("hello, ".toList ++ s ++ "\n".toList)], vs⟩ :: trace h)), fun n hn => ?_, rfl, vs,
    trace_set _ (by simp [Array.size_push]; omega)⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 20 := ⟨n - 20, by omega⟩
  exact greet_run I env0 h L s vs e k

/-- readings reads the clock twice, and the second reading is no earlier than the first -/
theorem readings_spec (I : Sem) (hI : I.oracle = real) (env0 : Env) (h : Heap) (L : Lib h) :
    RunP (readings I env0 []) h fun r h' => ∃ t0 t1 : Int, t0 ≤ t1 ∧ r = [timeVal t0, timeVal t1] ∧
      trace h' = ⟨"os.time", [], [.num (.int t1)]⟩ :: ⟨"os.time", [], [.num (.int t0)]⟩ :: trace h := by
  obtain ⟨t0, e0⟩ := clock_answers (trace h)
  obtain ⟨t1, e1⟩ := clock_answers (⟨"os.time", [], [.num (.int t0)]⟩ :: trace h)
  have le := clock_mono _ t1 t0 e1 List.mem_cons_self
  rw [← hI] at e0 e1
  have hs6 := lt_of_some L.log.choose_spec
  refine ⟨30, _, (((h.setIfInBounds LOG (.log (⟨"os.time", [], [.num (.int t0)]⟩ :: trace h))).push
    (.cell (timeVal t0))).setIfInBounds LOG
    (.log (⟨"os.time", [], [.num (.int t1)]⟩ :: ⟨"os.time", [], [.num (.int t0)]⟩ :: trace h))).push
    (.cell (timeVal t1)), fun n hn => ?_, t0, t1, le, rfl, ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 30 := ⟨n - 30, by omega⟩
    exact readings_run I env0 h L t0 t1 e0 e1 k
  · simp [trace_push, trace_set, Array.size_setIfInBounds, Array.size_push, hs6, Nat.lt_succ_of_lt]

/-- info: 'World.greet_spec' depends on axioms: [propext, Classical.choice, Quot.sound, takes_writes] -/
#guard_msgs in #print axioms greet_spec

/-- info: 'World.readings_spec' depends on axioms: [propext, Classical.choice, Quot.sound, clock_answers, clock_mono] -/
#guard_msgs in #print axioms readings_spec

end World
