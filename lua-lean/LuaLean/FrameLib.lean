import LuaLean.Frame

/-! `Keeps` of the semantics' helpers, the interpreter's calls aside (`LuaLean/FrameCall.lean`) -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Lua
section
variable {c : Nat} {P : Val → Prop}

theorem opErr_keeps {α : Type} {what : String} {i : Option Nat} {v : Val} :
    Keeps c P (opErr (α := α) what i v) fun _ => True := by
  unfold opErr; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact opErr_keeps)

theorem callerErr_keeps {α : Type} {msg : String} :
    Keeps c P (callerErr (α := α) msg) fun _ => True := by
  unfold callerErr; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact callerErr_keeps)

theorem argErr_keeps {α : Type} {narg : Nat} {msg : String} :
    Keeps c P (argErr (α := α) narg msg) fun _ => True := by
  unfold argErr; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact argErr_keeps)

theorem dumpBytes_keeps {α : Type} :
    Keeps c P (dumpBytes (α := α)) fun _ => True := by
  unfold dumpBytes; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact dumpBytes_keeps)

theorem noDump_keeps {v : Val} :
    Keeps c P (noDump v) fun _ => True := by
  unfold noDump; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact noDump_keeps)

theorem noDump2_keeps {x y : Val} :
    Keeps c P (noDump2 x y) fun _ => True := by
  unfold noDump2; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact noDump2_keeps)

theorem ffiStop_keeps {α : Type} {what : String} :
    Keeps c P (ffiStop (α := α) what) fun _ => True := by
  unfold ffiStop; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact ffiStop_keeps)

theorem noCdata_keeps {v : Val} :
    Keeps c P (noCdata v) fun _ => True := by
  unfold noCdata; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact noCdata_keeps)

theorem rawget_keeps {a : Nat} {k : Val} :
    Keeps c P (rawget a k) fun _ => True := by
  unfold rawget; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact rawget_keeps)

theorem weakOf_keeps {t : Tbl} :
    Keeps c P (weakOf t) fun _ => True := by
  unfold weakOf; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact weakOf_keeps)

theorem held_keeps {t : Tbl} {v : Val} :
    Keeps c P (held t v) fun _ => True := by
  unfold held; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact held_keeps)

theorem wget_keeps {a : Nat} {k : Val} :
    Keeps c P (wget a k) fun _ => True := by
  unfold wget; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact wget_keeps)

theorem tlen_keeps {a : Nat} :
    Keeps c P (tlen a) fun _ => True := by
  unfold tlen; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact tlen_keeps)

theorem tnext_keeps {a : Nat} {k : Val} :
    Keeps c P (tnext a k) fun _ => True := by
  unfold tnext; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact tnext_keeps)

theorem noI64Id_keeps {v : Val} :
    Keeps c P (noI64Id v) fun _ => True := by
  unfold noI64Id; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact noI64Id_keeps)

theorem rawset_keeps {a : Nat} {k v : Val} :
    Keeps c P (rawset a k v) fun _ => True := by
  unfold rawset; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact rawset_keeps)

theorem fenvOf_keeps {a : Nat} :
    Keeps c P (fenvOf a) fun _ => True := by
  unfold fenvOf; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact fenvOf_keeps)


/-! The frames of an error (`ERRF`) and the trace (`LOG`): fixed cells, not `c` -/

theorem Own.setSys {h : Heap} {a : Nat} {o : Obj} (ow : Own c P h) (ha : a ≤ 16) (ok : ObjOk c P o) :
    Own c P (h.set! a o) := ow.set (by have := ow.sys16; omega) ok

theorem errStep_own {f : List Frame → List Frame} {h : Heap} (o : Own c P h) : Own c P (errStep f h) := by
  unfold errStep; split
  · exact o.setSys (by simp [ERRF]) trivial
  · exact o

macro "wrap_fin" : tactic => `(tactic| ((try (injections; subst_vars)); first
  | (refine ⟨_, _, rfl, ?_⟩; first | assumption | exact errStep_own ‹_›)
  | (refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩; first | assumption | exact errStep_own ‹_›)
  | (simp at *; done)))

/-- `m` changed only in what its error is, or by a step of `ERRF` -/
theorem Keeps.wrap {α : Type} {m m' : M α} {Q : α → Prop} (hm : Keeps c P m Q)
    (hw : ∀ h, Own c P h → (∀ a h', m h = .ok a h' → m' h = .ok a h') ∧
      (∀ e h', m h = .error e h' → Own c P h' → ∃ e' h'', m' h = .error e' h'' ∧ Own c P h'')) :
    Keeps c P m' Q := by
  intro h o
  have r := hm h o
  cases e : m h with
  | ok a h' => rw [e] at r; rw [(hw h o).1 a h' e]; exact r
  | error er h' =>
    rw [e] at r
    obtain ⟨e', h'', e2, o2⟩ := (hw h o).2 er h' e r
    rw [e2]; exact o2

theorem onFrames_keeps {α : Type} {f : List Frame → List Frame} {m : M α} {Q : α → Prop} (hm : Keeps c P m Q) :
    Keeps c P (onFrames f m) Q := by
  refine Keeps.wrap hm fun h _ => ⟨fun a h' e => by simp [onFrames, e], fun er h' e o' => ?_⟩
  simp only [onFrames, e]; cases er <;> (try simp only [Err.isLua]) <;> (repeat' split) <;> wrap_fin
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine onFrames_keeps ?_))

theorem cFrame_keeps {α : Type} {v : Val} {m : M α} {Q : α → Prop} (hm : Keeps c P m Q) :
    Keeps c P (cFrame v m) Q := onFrames_keeps hm
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine cFrame_keeps ?_))

theorem mmName_keeps {α : Type} {ev : String} {m : M α} {Q : α → Prop} (hm : Keeps c P m Q) :
    Keeps c P (mmName ev m) Q := onFrames_keeps hm
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine mmName_keeps ?_))

theorem mmFrame_keeps {α : Type} {ev : String} {m : M α} {Q : α → Prop} (hm : Keeps c P m Q) :
    Keeps c P (mmFrame ev m) Q := by
  refine onFrames_keeps (Keeps.wrap hm fun h _ => ⟨fun a h' e => by simp [e], fun er h' e o' => ?_⟩)
  simp only [e]
  cases er with
  | rt k msg => cases k <;> cases msg <;> wrap_fin
  | _ => wrap_fin
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine mmFrame_keeps ?_))

theorem atSite_keeps {α : Type} {s : Site} {m : M α} {Q : α → Prop} (hm : Keeps c P m Q) :
    Keeps c P (atSite s m) Q := by
  refine Keeps.wrap hm fun h _ => ⟨fun a h' e => by simp [atSite, e], fun er h' e o' => ?_⟩
  simp only [atSite, e]; cases er <;> (try simp only [Err.isLua]) <;> (repeat' split) <;> wrap_fin
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine atSite_keeps ?_))

theorem atSite?_keeps {α : Type} {s : Option Site} {m : M α} {Q : α → Prop} (hm : Keeps c P m Q) :
    Keeps c P (atSite? s m) Q := by
  cases s
  · exact hm
  · exact atSite_keeps hm
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine atSite?_keeps ?_))

theorem unframe_keeps {α : Type} {m : M α} {Q : α → Prop} (hm : Keeps c P m Q) : Keeps c P (unframe m) Q := by
  refine Keeps.wrap hm fun h _ => ⟨fun a h' e => by simp [unframe, e], fun er h' e o' => ?_⟩
  simp only [unframe, e]; cases er <;> (try simp only [Err.isLua]) <;> (repeat' split) <;> wrap_fin
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine unframe_keeps ?_))

theorem frame_keeps {α : Type} {m : M α} {Q : α → Prop} (hm : Keeps c P m Q) : Keeps c P (frame m) Q := by
  refine Keeps.wrap hm fun h _ => ⟨fun a h' e => by simp [frame, e], fun er h' e o' => ?_⟩
  simp only [frame, e]; cases er <;> (try simp only [Err.isLua]) <;> (repeat' split) <;> wrap_fin
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine frame_keeps ?_))

theorem effect_keeps {oracle : Oracle} {name : String} {args : List Val} :
    Keeps c P (effect oracle name args) fun _ => True := by
  intro h o; simp only [effect]; cases oracle name args (trace h) with
  | some vs => exact ⟨o.setSys (by simp [LOG]) (by simp [ObjOk]), trivial⟩
  | none => exact o
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact effect_keeps)

theorem newClo_keeps {self : Nat} {ps : List String} {va : Bool} {b : Block} {env : Env} {ln : Nat × Nat}
    (he : EnvOk c env) : Keeps c P (newClo self ps va b env ln) fun _ => True := by
  unfold newClo; refine Keeps.bind getObj_keeps fun o _ => ?_; split
  · exact (alloc_keeps (by exact he)).mono fun _ _ => trivial
  · exact Keeps.throw
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine newClo_keeps ?_; keeps_side))

theorem bindLocals_keeps {cx : Ctx} {xs : List String} {vs : List Val} (he : EnvOk c cx.env) :
    Keeps c P (bindLocals cx xs vs) fun cx' => EnvOk c cx'.env := by
  induction xs generalizing cx vs with
  | nil => exact Keeps.pure he
  | cons x xs ih =>
    unfold bindLocals
    refine Keeps.bind (alloc_keeps trivial) fun a ha => ih ?_
    intro y hy; simp only [List.mem_cons] at hy; rcases hy with rfl | hy
    · exact ha
    · exact he y hy
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine bindLocals_keeps ?_; keeps_side))

theorem getThr_keeps {a : Nat} : Keeps c P (getThr a) fun t => a ≠ c ∧ ThrOk c P t := by
  unfold getThr; refine Keeps.bind getObj_keeps fun o ho => ?_
  split
  · exact Keeps.pure ⟨ho.2 (by simp), ho.1⟩
  · exact Keeps.throw
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact getThr_keeps)

theorem putThr_keeps {a : Nat} {t : Thr Heap} (ne : a ≠ c) (ok : ThrOk c P t) :
    Keeps c P (putThr a t) fun _ => True := modify_set_keeps ne ok
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine putThr_keeps ?_ ?_ <;> keeps_side))


theorem metaOf_keeps {v : Val} {ev : String} : Keeps c P (metaOf v ev) fun _ => True := by
  unfold metaOf; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact metaOf_keeps)

theorem bounded_keeps {α : Type} {b : Nat} {m : M α} {Q : α → Prop} (hm : Keeps c P m Q) :
    Keeps c P (bounded b m) Q := by
  unfold bounded; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine bounded_keeps ?_))

theorem resumeBegin_keeps {a : Nat} {args : List Val} :
    Keeps c P (resumeBegin a args) fun r => ∀ x, r = .ok x → HeapsOk c P x.2.1 := by
  unfold resumeBegin; keeps

macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact resumeBegin_keeps)

theorem coRun_keeps {x : M (List Val)} (hx : Keeps c P x fun _ => True) :
    Keeps c P (coRun x) fun _ => True := by
  intro h o; have r := hx h o; simp only [coRun]; revert r
  cases x h with
  | ok a h' => intro r; exact ⟨r.1, trivial⟩
  | error e h' => intro r; cases e <;> simp only <;> first | exact ⟨errStep_own r, trivial⟩ | exact ⟨r, trivial⟩ | exact r
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine coRun_keeps ?_))

theorem resumeEnd_keeps {a : Nat} {prev : Val} {hist : List (List Val × Heap)} {r : Except Val (Bool × List Val)}
    (hh : HeapsOk c P hist) : Keeps c P (resumeEnd a prev hist r) fun _ => True := by
  unfold resumeEnd; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible (refine resumeEnd_keeps ?_; keeps_side))

theorem yieldFn_keeps {args : List Val} : Keeps c P (yieldFn args) fun _ => True := by
  unfold yieldFn; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact yieldFn_keeps)

theorem metaFn_keeps {h_ : Val} :
    Keeps c P (metaFn h_) fun _ => True := by
  unfold metaFn; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact metaFn_keeps)

theorem metaOf2_keeps {ev : String} {x y : Val} :
    Keeps c P (metaOf2 ev x y) fun _ => True := by
  unfold metaOf2; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact metaOf2_keeps)

theorem compErr_keeps {α : Type} {x y : Val} :
    Keeps c P (compErr (α := α) x y) fun _ => True := by
  unfold compErr; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact compErr_keeps)

theorem anyArg_keeps {i : Nat} {args : List Val} :
    Keeps c P (anyArg i args) fun _ => True := by
  unfold anyArg; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact anyArg_keeps)

theorem badType_keeps {α : Type} {what : String} {i : Nat} {args : List Val} :
    Keeps c P (badType (α := α) what i args) fun _ => True := by
  unfold badType; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact badType_keeps)

theorem argStr_keeps {_fname : String} {i : Nat} {args : List Val} :
    Keeps c P (argStr _fname i args) fun _ => True := by
  unfold argStr; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact argStr_keeps)

theorem argNum_keeps {_fname : String} {i : Nat} {args : List Val} :
    Keeps c P (argNum _fname i args) fun _ => True := by
  unfold argNum; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact argNum_keeps)

theorem argIntN_keeps {bits : Nat} {fname : String} {i : Nat} {args : List Val} :
    Keeps c P (argIntN bits fname i args) fun _ => True := by
  unfold argIntN; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact argIntN_keeps)

theorem argInt_keeps {fname : String} {i : Nat} {args : List Val} :
    Keeps c P (argInt fname i args) fun _ => True := by
  unfold argInt; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact argInt_keeps)

theorem optInt_keeps {fname : String} {i : Nat} {args : List Val} {d : Int} :
    Keeps c P (optInt fname i args d) fun _ => True := by
  unfold optInt; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact optInt_keeps)

theorem argFn_keeps {_fname : String} {i : Nat} {args : List Val} :
    Keeps c P (argFn _fname i args) fun _ => True := by
  unfold argFn; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact argFn_keeps)

theorem argTbl_keeps {_fname : String} {i : Nat} {args : List Val} :
    Keeps c P (argTbl _fname i args) fun _ => True := by
  unfold argTbl; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact argTbl_keeps)

theorem i64Exact_keeps {v : Val} :
    Keeps c P (i64Exact v) fun _ => True := by
  unfold i64Exact; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact i64Exact_keeps)

theorem strFind_keeps {find : Bool} {args : List Val} :
    Keeps c P (strFind find args) fun _ => True := by
  unfold strFind; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact strFind_keeps)

theorem gmatchStep_go_keeps {s : List Char} {cell : Nat} {ms : Pat.MS} {fuel src k : Nat} :
    Keeps c P (gmatchStep.go s cell ms fuel src k) fun _ => True := by
  induction k generalizing src with
  | zero => unfold gmatchStep.go; keeps
  | succ k ih => unfold gmatchStep.go; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact gmatchStep_go_keeps)

theorem gmatchStep_keeps {s p : List Char} {cell : Nat} :
    Keeps c P (gmatchStep s p cell) fun _ => True := by
  unfold gmatchStep; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact gmatchStep_keeps)

theorem mathFn_keeps {name : String} {args : List Val} :
    Keeps c P (mathFn name args) fun _ => True := by
  unfold mathFn; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact mathFn_keeps)

theorem argBit_keeps {fname : String} {i : Nat} {args : List Val} :
    Keeps c P (argBit fname i args) fun _ => True := by
  unfold argBit; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact argBit_keeps)

theorem bitFn_keeps {name : String} {args : List Val} :
    Keeps c P (bitFn name args) fun _ => True := by
  unfold bitFn; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact bitFn_keeps)

theorem i64Bits_keeps {u : Bool} {x : CNum} : Keeps c P (i64Bits u x) fun _ => True := by
  unfold i64Bits; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact i64Bits_keeps)

theorem cdeclsOf_keeps  :
    Keeps c P (cdeclsOf ) fun _ => True := by
  unfold cdeclsOf; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdeclsOf_keeps)

theorem ctMeta_keeps {t : CType} {ev : String} :
    Keeps c P (ctMeta t ev) fun _ => True := by
  unfold ctMeta; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact ctMeta_keeps)

theorem ctName_keeps {t : CType} :
    Keeps c P (ctName t) fun _ => True := by
  unfold ctName; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact ctName_keeps)

theorem getBytes_keeps {m : Nat} : Keeps c P (getBytes m) fun _ => m ≠ c := by
  unfold getBytes; refine Keeps.bind getObj_keeps fun o ho => ?_
  split
  · exact Keeps.pure (ho.2 (by simp))
  · exact Keeps.pure (ho.2 (by simp))
  · exact Keeps.throw
  · exact Keeps.throw
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact getBytes_keeps)

theorem readMem_keeps {m off len : Nat} :
    Keeps c P (readMem m off len) fun _ => True := by
  unfold readMem; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact readMem_keeps)

theorem writeMem_keeps {m off : Nat} {bs : List UInt8} :
    Keeps c P (writeMem m off bs) fun _ => True := by
  unfold writeMem; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact writeMem_keeps)

theorem zeroMem_keeps {m off len : Nat} :
    Keeps c P (zeroMem m off len) fun _ => True := by
  unfold zeroMem; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact zeroMem_keeps)

theorem numToInt_keeps {x : Float} :
    Keeps c P (numToInt x) fun _ => True := by
  unfold numToInt; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact numToInt_keeps)

theorem intToFloat_keeps {i : Int} :
    Keeps c P (intToFloat i) fun _ => True := by
  unfold intToFloat; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact intToFloat_keeps)

theorem encode_keeps {t : CType} {x : CNum} :
    Keeps c P (encode t x) fun _ => True := by
  unfold encode; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact encode_keeps)

theorem decode_keeps {t : CType} {bs : List UInt8} :
    Keeps c P (decode t bs) fun _ => True := by
  unfold decode; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact decode_keeps)

theorem getCd_keeps {a : Nat} :
    Keeps c P (getCd a) fun _ => True := by
  unfold getCd; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact getCd_keeps)

theorem CErr.raise_keeps {α : Type} {e : CErr} {msg : String} :
    Keeps c P (CErr.raise (α := α) e msg) fun _ => True := by
  unfold CErr.raise; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact CErr.raise_keeps)

theorem convErr_keeps {α : Type} {e : CErr} {src : String} {dst : CType} :
    Keeps c P (convErr (α := α) e src dst) fun _ => True := by
  unfold convErr; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact convErr_keeps)

theorem cdName_keeps {ct : CType} :
    Keeps c P (cdName ct) fun _ => True := by
  unfold cdName; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdName_keeps)

theorem srcName_keeps {v : Val} :
    Keeps c P (srcName v) fun _ => True := by
  unfold srcName; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact srcName_keeps)

theorem srcNum_keeps {e : CErr} {d : CType} {v : Val} {cast : Bool} :
    Keeps c P (srcNum e d v cast) fun _ => True := by
  unfold srcNum; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact srcNum_keeps)

theorem initOv_keeps {α : Type} {e : CErr} {d : CType} :
    Keeps c P (initOv (α := α) e d) fun _ => True := by
  unfold initOv; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact initOv_keeps)

theorem sameAgg_keeps {d : CType} {v : Val} :
    Keeps c P (sameAgg d v) fun _ => True := by
  unfold sameAgg; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact sameAgg_keeps)

theorem cdBytes_keeps {v : Val} {len : Nat} :
    Keeps c P (cdBytes v len) fun _ => True := by
  unfold cdBytes; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdBytes_keeps)

theorem memSize_keeps {m : Nat} :
    Keeps c P (memSize m) fun _ => True := by
  unfold memSize; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact memSize_keeps)

theorem sameMem_keeps {m m' : Nat} :
    Keeps c P (sameMem m m') fun _ => True := by
  unfold sameMem; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact sameMem_keeps)



theorem addrEq_keeps {p q : Option (Nat × Nat)} : Keeps c P (addrEq p q) fun _ => True := by
  unfold addrEq; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact addrEq_keeps)

theorem cIdx_keeps {x : CNum} : Keeps c P (cIdx x) fun _ => True := by
  unfold cIdx; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cIdx_keeps)

theorem toPtr_keeps {e : CErr} {d : CType} {v : Val} {cast : Bool} {dn : Option String} :
    Keeps c P (toPtr e d v cast dn) fun _ => True := by
  unfold toPtr; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact toPtr_keeps)

theorem fill_rep_keeps {esz sz m off : Nat} {el : List UInt8} {k o : Nat} :
    Keeps c P (fill.rep esz sz m off el k o) fun _ => True := by
  induction k generalizing o with
  | zero => unfold fill.rep; keeps
  | succ k ih => unfold fill.rep; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact fill_rep_keeps)

theorem fill_keeps {k : Nat} {d : CType} {m off sz ofs esz : Nat} :
    Keeps c P (fill k d m off sz ofs esz) fun _ => True := by
  unfold fill; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact fill_keeps)

/-- the FFI's stores, on their fuel -/
theorem store_keeps_all (k : Nat) :
    (∀ e d0 m off v, Keeps c P (store k e d0 m off v) fun _ => True) ∧
    (∀ e d et sz m off t, Keeps c P (arrTab k e d et sz m off t) fun _ => True) ∧
    (∀ e d et sz m off t esz i ofs, Keeps c P (arrTab.go e d et sz m off t esz k i ofs) fun _ => True) ∧
    (∀ e u fs m off t i first, Keeps c P (aggTab k e u fs m off t i first) fun _ => True) := by
  induction k with
  | zero =>
    refine ⟨fun _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ => ?_⟩ <;>
      first | (unfold store; keeps) | (unfold arrTab; keeps) | (unfold arrTab.go; keeps) | (unfold aggTab; keeps)
  | succ k ih =>
    obtain ⟨hs, ha, hg, hagg⟩ := ih
    have hs' : ∀ e d0 m off v, Keeps c P (store k e d0 m off v) fun _ => True := hs
    refine ⟨fun _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ _ _ => ?_, fun _ _ _ _ _ _ _ _ => ?_⟩
    · unfold store; keeps <;> first | exact ha _ _ _ _ _ _ _ | exact hagg _ _ _ _ _ _ _ _
    · unfold arrTab; keeps <;> exact hg _ _ _ _ _ _ _ _ _ _
    · unfold arrTab.go; keeps <;> first | exact hs _ _ _ _ _ | exact hg _ _ _ _ _ _ _ _ _ _
    · unfold aggTab; keeps <;> first | exact hs _ _ _ _ _ | exact hagg _ _ _ _ _ _ _ _

theorem store_keeps {k : Nat} {e : CErr} {d0 : CType} {m off : Nat} {v : Val} :
    Keeps c P (store k e d0 m off v) fun _ => True := (store_keeps_all k).1 _ _ _ _ _
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact store_keeps)


theorem cdInitArr_keeps {e : CErr} {d et : CType} {m sz : Nat} {vs : List Val} :
    Keeps c P (cdInitArr e d et m sz vs) fun _ => True := by
  unfold cdInitArr; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdInitArr_keeps)

theorem cdInitAgg_keeps {e : CErr} {d : CType} {m sz : Nat} {vs : List Val} :
    Keeps c P (cdInitAgg e d m sz vs) fun _ => True := by
  unfold cdInitAgg; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdInitAgg_keeps)

theorem asItself_keeps {d : CType} {v : Val} :
    Keeps c P (asItself d v) fun _ => True := by
  unfold asItself; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact asItself_keeps)

theorem cdInit_keeps {e : CErr} {d0 : CType} {m sz : Nat} {vs : List Val} :
    Keeps c P (cdInit e d0 m sz vs) fun _ => True := by
  unfold cdInit; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdInit_keeps)

theorem box_keeps {t : CType} {bs : List UInt8} :
    Keeps c P (box t bs) fun _ => True := by
  unfold box; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact box_keeps)

theorem cdNew_keeps {ct : CType} {sz : Nat} :
    Keeps c P (cdNew ct sz) fun _ => True := by
  unfold cdNew; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdNew_keeps)

theorem toLua_keeps {t : CType} {bs : List UInt8} :
    Keeps c P (toLua t bs) fun _ => True := by
  unfold toLua; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact toLua_keeps)

theorem idxErr_keeps {α : Type} {t : CType} {k : Val} :
    Keeps c P (idxErr (α := α) t k) fun _ => True := by
  unfold idxErr; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact idxErr_keeps)

theorem cdLookup_keeps {t : CType} {q : Bool} {m off : Nat} {k : Val} :
    Keeps c P (cdLookup t q m off k) fun _ => True := by
  unfold cdLookup; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdLookup_keeps)

theorem ptrLookup_keeps {ct : CType} {p : Option (Nat × Nat)} {k : Val} :
    Keeps c P (ptrLookup ct p k) fun _ => True := by
  unfold ptrLookup; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact ptrLookup_keeps)

theorem cdPlace_keeps {a : Nat} {k : Val} :
    Keeps c P (cdPlace a k) fun _ => True := by
  unfold cdPlace; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdPlace_keeps)

theorem cdIndex_keeps {a : Nat} {k : Val} :
    Keeps c P (cdIndex a k) fun _ => True := by
  unfold cdIndex; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdIndex_keeps)

theorem cdSet_keeps {a : Nat} {k v : Val} :
    Keeps c P (cdSet a k v) fun _ => True := by
  unfold cdSet; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdSet_keeps)

theorem cOp_keeps {v : Val} :
    Keeps c P (cOp v) fun _ => True := by
  unfold cOp; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cOp_keeps)

theorem cOpName_keeps {v : Val} :
    Keeps c P (cOpName v) fun _ => True := by
  unfold cOpName; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cOpName_keeps)

theorem i64Pair_keeps {x : CNum} {xu : Bool} {y : CNum} {yu : Bool} :
    Keeps c P (i64Pair x xu y yu) fun _ => True := by
  unfold i64Pair; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact i64Pair_keeps)

theorem eqAddr_keeps {p : Option (Nat × Nat)} {y : Val} :
    Keeps c P (eqAddr p y) fun _ => True := by
  unfold eqAddr; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact eqAddr_keeps)

theorem ptrish_keeps {v : Val} :
    Keeps c P (ptrish v) fun _ => True := by
  unfold ptrish; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact ptrish_keeps)

theorem cdEq_keeps {a : Nat} {y : Val} :
    Keeps c P (cdEq a y) fun _ => True := by
  unfold cdEq; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdEq_keeps)

theorem cdAddrEq_keeps {x y : Val} :
    Keeps c P (cdAddrEq x y) fun _ => True := by
  unfold cdAddrEq; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdAddrEq_keeps)

theorem opMeta_keeps {v : Val} {ev : String} :
    Keeps c P (opMeta v ev) fun _ => True := by
  unfold opMeta; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact opMeta_keeps)

theorem opMeta2_keeps {ev : String} {x y : Val} :
    Keeps c P (opMeta2 ev x y) fun _ => True := by
  unfold opMeta2; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact opMeta2_keeps)

theorem cdArith_keeps {name : String} {args : List Val} :
    Keeps c P (cdArith name args) fun _ => True := by
  unfold cdArith; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdArith_keeps)

theorem cdArithErr_keeps {α : Type} {name : String} {x y : Val} :
    Keeps c P (cdArithErr (α := α) name x y) fun _ => True := by
  unfold cdArithErr; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdArithErr_keeps)

theorem cdLess_keeps {x y : Val} {orEq : Bool} :
    Keeps c P (cdLess x y orEq) fun _ => True := by
  unfold cdLess; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact cdLess_keeps)

theorem ctArg_keeps {args : List Val} :
    Keeps c P (ctArg args) fun _ => True := by
  unfold ctArg; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact ctArg_keeps)

theorem intArg_keeps {args : List Val} {k : Nat} :
    Keeps c P (intArg args k) fun _ => True := by
  unfold intArg; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact intArg_keeps)

theorem ffiNew_keeps {args : List Val} :
    Keeps c P (ffiNew args) fun _ => True := by
  unfold ffiNew; keeps
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible exact ffiNew_keeps)

end
end Lua
