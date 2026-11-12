import LuaLean.FrameLib

/-! The frame rule for the interpreter's calls: from a heap where `c` is its function's own (`Own`), every function
of the interpreter's mutual block, at any fuel, ends in a heap where `c` is still own (`call_keeps`) -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Lua
section
variable (c : Nat) (P : Val → Prop) (srcs : String → Option Block) (oracle : Oracle) (tgt : Target)

/-- every function of the mutual block at fuel `n` keeps `c` own, of a context whose environment does not hold it -/
structure AllK (n : Nat) : Prop where
  eval : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Exp), Keeps c P (Lua.eval srcs oracle tgt n cx x1) fun _ => True
  evalMulti : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Exp), Keeps c P (Lua.evalMulti srcs oracle tgt n cx x1) fun _ => True
  evalList : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List Exp), Keeps c P (Lua.evalList srcs oracle tgt n cx x1) fun _ => True
  tableCons : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List Field), Keeps c P (Lua.tableCons srcs oracle tgt n cx x1) fun _ => True
  fields : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Nat) (x2 : List Field), Keeps c P (Lua.fields srcs oracle tgt n cx x1 x2) fun _ => True
  index : ∀ (x0 : Val) (x1 : Val), Keeps c P (Lua.index srcs oracle tgt n x0 x1) fun _ => True
  cdMetaIndex : ∀ (x0 : CType) (x1 : Val) (x2 : Val), Keeps c P (Lua.cdMetaIndex srcs oracle tgt n x0 x1 x2) fun _ => True
  cdMetaGet : ∀ (x0 : CType) (x1 : Val) (x2 : Val), Keeps c P (Lua.cdMetaGet srcs oracle tgt n x0 x1 x2) fun _ => True
  call : ∀ (x0 : Val) (x1 : List Val), Keeps c P (Lua.call srcs oracle tgt n x0 x1) fun _ => True
  execBlock : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Block), Keeps c P (Lua.execBlock srcs oracle tgt n cx x1) fun _ => True
  execSeq : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Block) (x2 : Block) (x3 : Option Exp), Keeps c P (Lua.execSeq srcs oracle tgt n cx x1 x2 x3) fun _ => True
  execStat : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Stat), Keeps c P (Lua.execStat srcs oracle tgt n cx x1) fun _ => True
  places : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List Exp), Keeps c P (Lua.places srcs oracle tgt n cx x1) fun _ => True
  assign : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List (String ⊕ Val × Val × Option Site)) (x2 : List Val), Keeps c P (Lua.assign srcs oracle tgt n cx x1 x2) fun _ => True
  setindex : ∀ (x0 : Val) (x1 : Val) (x2 : Val), Keeps c P (Lua.setindex srcs oracle tgt n x0 x1 x2) fun _ => True
  binop : ∀ (x0 : BinOp) (x1 : Val) (x2 : Val), Keeps c P (Lua.binop srcs oracle tgt n x0 x1 x2) fun _ => True
  less : ∀ (x0 : Val) (x1 : Val) (x2 : Bool) (x3 : Option String), Keeps c P (Lua.less srcs oracle tgt n x0 x1 x2 x3) fun _ => True
  eqv : ∀ (x0 : Val) (x1 : Val), Keeps c P (Lua.eqv srcs oracle tgt n x0 x1) fun _ => True
  printArgs : ∀ (x0 : List Val) (x1 : List Char) (x2 : Bool), Keeps c P (Lua.printArgs srcs oracle tgt n x0 x1 x2) fun _ => True
  unop : ∀ (x0 : UnOp) (x1 : Val), Keeps c P (Lua.unop srcs oracle tgt n x0 x1) fun _ => True
  whileLoop : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Exp) (x2 : Block), Keeps c P (Lua.whileLoop srcs oracle tgt n cx x1 x2) fun _ => True
  rptLoop : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Block) (x2 : Exp), Keeps c P (Lua.rptLoop srcs oracle tgt n cx x1 x2) fun _ => True
  numLoop : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : String) (x2 : Num) (x3 : Num) (x4 : Num) (x5 : Block), Keeps c P (Lua.numLoop srcs oracle tgt n cx x1 x2 x3 x4 x5) fun _ => True
  iterCall : ∀ (x0 : Val) (x1 : Val) (x2 : Val), Keeps c P (Lua.iterCall srcs oracle tgt n x0 x1 x2) fun _ => True
  inLoop : ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List String) (x2 : Val) (x3 : Val) (x4 : Val) (x5 : Block), Keeps c P (Lua.inLoop srcs oracle tgt n cx x1 x2 x3 x4 x5) fun _ => True
  callPrim : ∀ (x0 : String) (x1 : List Val) (x2 : List Val), Keeps c P (Lua.callPrim srcs oracle tgt n x0 x1 x2) fun _ => True
  readChunk : ∀ (x0 : Val) (x1 : List Char), Keeps c P (Lua.readChunk srcs oracle tgt n x0 x1) fun _ => True
  foreachi : ∀ (x0 : Nat) (x1 : Val) (x2 : Int) (x3 : Int), Keeps c P (Lua.foreachi srcs oracle tgt n x0 x1 x2 x3) fun _ => True
  foreachK : ∀ (x0 : Nat) (x1 : Val) (x2 : Val), Keeps c P (Lua.foreachK srcs oracle tgt n x0 x1 x2) fun _ => True
  lessThan : ∀ (x0 : Val) (x1 : Val) (x2 : Val), Keeps c P (Lua.lessThan srcs oracle tgt n x0 x1 x2) fun _ => True
  sortAux : ∀ (x0 : Nat) (x1 : Val) (x2 : Int) (x3 : Int), Keeps c P (Lua.sortAux srcs oracle tgt n x0 x1 x2 x3) fun _ => True
  sortPart : ∀ (x0 : Nat) (x1 : Val) (x2 : Val) (x3 : Int) (x4 : Int) (x5 : Int) (x6 : Int), Keeps c P (Lua.sortPart srcs oracle tgt n x0 x1 x2 x3 x4 x5 x6) fun _ => True
  sortUp : ∀ (x0 : Nat) (x1 : Val) (x2 : Val) (x3 : Int) (x4 : Int), Keeps c P (Lua.sortUp srcs oracle tgt n x0 x1 x2 x3 x4) fun _ => True
  sortDown : ∀ (x0 : Nat) (x1 : Val) (x2 : Val) (x3 : Int) (x4 : Int), Keeps c P (Lua.sortDown srcs oracle tgt n x0 x1 x2 x3 x4) fun _ => True
  gsub : ∀ (x0 : List Val), Keeps c P (Lua.gsub srcs oracle tgt n x0) fun _ => True
  gsubGo : ∀ (x0 : Pat.MS) (x1 : Val) (x2 : Bool) (x3 : Int) (x4 : Nat) (x5 : Nat) (x6 : List Char), Keeps c P (Lua.gsubGo srcs oracle tgt n x0 x1 x2 x3 x4 x5 x6) fun _ => True
  addValue : ∀ (x0 : Pat.MS) (x1 : Val) (x2 : Array Pat.Cap) (x3 : Nat) (x4 : Nat), Keeps c P (Lua.addValue srcs oracle tgt n x0 x1 x2 x3 x4) fun _ => True

end

section
variable {c : Nat} {P : Val → Prop} {srcs : String → Option Block} {oracle : Oracle} {tgt : Target}

theorem EnvOk.lookup' {env : Env} {x : String} {a : Nat} (e : env.lookup x = some a) (h : EnvOk c env) : a ≠ c :=
  h _ (lookup_mem e)
macro_rules | `(tactic| keeps_side) => `(tactic| (apply EnvOk.lookup' <;> assumption))
@[simp] theorem fileClo_env {p : String} {b : Block} : (fileClo p b).env = [] := rfl

open Lean Meta Elab Tactic in
/-- a hypothesis that keeps (`AllK`'s fields: a function of the block at a lower fuel), applied: the first that fits -/
elab "keeps_hyp" : tactic => withMainContext do
  let g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless ← forallTelescope d.type fun _ b => pure (b.isAppOf ``Keeps) do continue
    if let some gs ← observing? (g.apply d.toExpr) then replaceMainGoal gs; return
  throwError "keeps_hyp: no hypothesis fits"
macro_rules | `(tactic| keeps_leaf) => `(tactic| with_reducible keeps_hyp)

set_option maxHeartbeats 4000000 in
theorem eval_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Exp), Keeps c P (eval srcs oracle tgt 0 cx x1) fun _ => True := by
  intros; unfold eval; keeps

set_option maxHeartbeats 4000000 in
theorem evalMulti_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Exp), Keeps c P (evalMulti srcs oracle tgt 0 cx x1) fun _ => True := by
  intros; unfold evalMulti; keeps

set_option maxHeartbeats 4000000 in
theorem evalList_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List Exp), Keeps c P (evalList srcs oracle tgt 0 cx x1) fun _ => True := by
  intros; unfold evalList; keeps

set_option maxHeartbeats 4000000 in
theorem tableCons_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List Field), Keeps c P (tableCons srcs oracle tgt 0 cx x1) fun _ => True := by
  intros; unfold tableCons; keeps

set_option maxHeartbeats 4000000 in
theorem fields_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Nat) (x2 : List Field), Keeps c P (fields srcs oracle tgt 0 cx x1 x2) fun _ => True := by
  intros; unfold fields; keeps

set_option maxHeartbeats 4000000 in
theorem index_zero :
    ∀ (x0 : Val) (x1 : Val), Keeps c P (index srcs oracle tgt 0 x0 x1) fun _ => True := by
  intros; unfold index; keeps

set_option maxHeartbeats 4000000 in
theorem cdMetaIndex_zero :
    ∀ (x0 : CType) (x1 : Val) (x2 : Val), Keeps c P (cdMetaIndex srcs oracle tgt 0 x0 x1 x2) fun _ => True := by
  intros; unfold cdMetaIndex; keeps

set_option maxHeartbeats 4000000 in
theorem cdMetaGet_zero :
    ∀ (x0 : CType) (x1 : Val) (x2 : Val), Keeps c P (cdMetaGet srcs oracle tgt 0 x0 x1 x2) fun _ => True := by
  intros; unfold cdMetaGet; keeps

set_option maxHeartbeats 4000000 in
theorem call_zero :
    ∀ (x0 : Val) (x1 : List Val), Keeps c P (call srcs oracle tgt 0 x0 x1) fun _ => True := by
  intros; unfold call; keeps

set_option maxHeartbeats 4000000 in
theorem execBlock_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Block), Keeps c P (execBlock srcs oracle tgt 0 cx x1) fun _ => True := by
  intros; unfold execBlock; keeps

set_option maxHeartbeats 4000000 in
theorem execSeq_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Block) (x2 : Block) (x3 : Option Exp), Keeps c P (execSeq srcs oracle tgt 0 cx x1 x2 x3) fun _ => True := by
  intros; unfold execSeq; keeps

set_option maxHeartbeats 4000000 in
theorem execStat_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Stat), Keeps c P (execStat srcs oracle tgt 0 cx x1) fun _ => True := by
  intros; unfold execStat; keeps

set_option maxHeartbeats 4000000 in
theorem places_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List Exp), Keeps c P (places srcs oracle tgt 0 cx x1) fun _ => True := by
  intros; unfold places; keeps

set_option maxHeartbeats 4000000 in
theorem assign_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List (String ⊕ Val × Val × Option Site)) (x2 : List Val), Keeps c P (assign srcs oracle tgt 0 cx x1 x2) fun _ => True := by
  intros; unfold assign; keeps

set_option maxHeartbeats 4000000 in
theorem setindex_zero :
    ∀ (x0 : Val) (x1 : Val) (x2 : Val), Keeps c P (setindex srcs oracle tgt 0 x0 x1 x2) fun _ => True := by
  intros; unfold setindex; keeps

set_option maxHeartbeats 4000000 in
theorem less_zero :
    ∀ (x0 : Val) (x1 : Val) (x2 : Bool) (x3 : Option String), Keeps c P (less srcs oracle tgt 0 x0 x1 x2 x3) fun _ => True := by
  intros; unfold less; keeps

set_option maxHeartbeats 4000000 in
theorem eqv_zero :
    ∀ (x0 : Val) (x1 : Val), Keeps c P (eqv srcs oracle tgt 0 x0 x1) fun _ => True := by
  intros; unfold eqv; keeps

set_option maxHeartbeats 4000000 in
theorem printArgs_zero :
    ∀ (x0 : List Val) (x1 : List Char) (x2 : Bool), Keeps c P (printArgs srcs oracle tgt 0 x0 x1 x2) fun _ => True := by
  intros; unfold printArgs; keeps

set_option maxHeartbeats 4000000 in
theorem unop_zero :
    ∀ (x0 : UnOp) (x1 : Val), Keeps c P (unop srcs oracle tgt 0 x0 x1) fun _ => True := by
  intros; unfold unop; keeps

set_option maxHeartbeats 4000000 in
theorem whileLoop_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Exp) (x2 : Block), Keeps c P (whileLoop srcs oracle tgt 0 cx x1 x2) fun _ => True := by
  intros; unfold whileLoop; keeps

set_option maxHeartbeats 4000000 in
theorem rptLoop_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Block) (x2 : Exp), Keeps c P (rptLoop srcs oracle tgt 0 cx x1 x2) fun _ => True := by
  intros; unfold rptLoop; keeps

set_option maxHeartbeats 4000000 in
theorem numLoop_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : String) (x2 : Num) (x3 : Num) (x4 : Num) (x5 : Block), Keeps c P (numLoop srcs oracle tgt 0 cx x1 x2 x3 x4 x5) fun _ => True := by
  intros; unfold numLoop; keeps

set_option maxHeartbeats 4000000 in
theorem inLoop_zero :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List String) (x2 : Val) (x3 : Val) (x4 : Val) (x5 : Block), Keeps c P (inLoop srcs oracle tgt 0 cx x1 x2 x3 x4 x5) fun _ => True := by
  intros; unfold inLoop; keeps

set_option maxHeartbeats 4000000 in
theorem callPrim_zero :
    ∀ (x0 : String) (x1 : List Val) (x2 : List Val), Keeps c P (callPrim srcs oracle tgt 0 x0 x1 x2) fun _ => True := by
  intros; unfold callPrim; keeps

set_option maxHeartbeats 4000000 in
theorem readChunk_zero :
    ∀ (x0 : Val) (x1 : List Char), Keeps c P (readChunk srcs oracle tgt 0 x0 x1) fun _ => True := by
  intros; unfold readChunk; keeps

set_option maxHeartbeats 4000000 in
theorem foreachi_zero :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Int) (x3 : Int), Keeps c P (foreachi srcs oracle tgt 0 x0 x1 x2 x3) fun _ => True := by
  intros; unfold foreachi; keeps

set_option maxHeartbeats 4000000 in
theorem foreachK_zero :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Val), Keeps c P (foreachK srcs oracle tgt 0 x0 x1 x2) fun _ => True := by
  intros; unfold foreachK; keeps

set_option maxHeartbeats 4000000 in
theorem lessThan_zero :
    ∀ (x0 : Val) (x1 : Val) (x2 : Val), Keeps c P (lessThan srcs oracle tgt 0 x0 x1 x2) fun _ => True := by
  intros; unfold lessThan; keeps

set_option maxHeartbeats 4000000 in
theorem sortAux_zero :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Int) (x3 : Int), Keeps c P (sortAux srcs oracle tgt 0 x0 x1 x2 x3) fun _ => True := by
  intros; unfold sortAux; keeps

set_option maxHeartbeats 4000000 in
theorem sortPart_zero :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Val) (x3 : Int) (x4 : Int) (x5 : Int) (x6 : Int), Keeps c P (sortPart srcs oracle tgt 0 x0 x1 x2 x3 x4 x5 x6) fun _ => True := by
  intros; unfold sortPart; keeps

set_option maxHeartbeats 4000000 in
theorem sortUp_zero :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Val) (x3 : Int) (x4 : Int), Keeps c P (sortUp srcs oracle tgt 0 x0 x1 x2 x3 x4) fun _ => True := by
  intros; unfold sortUp; keeps

set_option maxHeartbeats 4000000 in
theorem sortDown_zero :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Val) (x3 : Int) (x4 : Int), Keeps c P (sortDown srcs oracle tgt 0 x0 x1 x2 x3 x4) fun _ => True := by
  intros; unfold sortDown; keeps

set_option maxHeartbeats 4000000 in
theorem gsub_zero :
    ∀ (x0 : List Val), Keeps c P (gsub srcs oracle tgt 0 x0) fun _ => True := by
  intros; unfold gsub; keeps

set_option maxHeartbeats 4000000 in
theorem gsubGo_zero :
    ∀ (x0 : Pat.MS) (x1 : Val) (x2 : Bool) (x3 : Int) (x4 : Nat) (x5 : Nat) (x6 : List Char), Keeps c P (gsubGo srcs oracle tgt 0 x0 x1 x2 x3 x4 x5 x6) fun _ => True := by
  intros; unfold gsubGo; keeps

set_option maxHeartbeats 4000000 in
theorem addValue_zero :
    ∀ (x0 : Pat.MS) (x1 : Val) (x2 : Array Pat.Cap) (x3 : Nat) (x4 : Nat), Keeps c P (addValue srcs oracle tgt 0 x0 x1 x2 x3 x4) fun _ => True := by
  intros; unfold addValue; keeps

set_option maxHeartbeats 4000000 in
theorem binop_zero :
    ∀ (x0 : BinOp) (x1 : Val) (x2 : Val), Keeps c P (binop srcs oracle tgt 0 x0 x1 x2) fun _ => True := by
  have := eqv_zero (c := c) (P := P) (srcs := srcs) (oracle := oracle) (tgt := tgt); have := less_zero (c := c) (P := P) (srcs := srcs) (oracle := oracle) (tgt := tgt); intros; unfold binop; keeps

set_option maxHeartbeats 4000000 in
theorem iterCall_zero :
    ∀ (x0 : Val) (x1 : Val) (x2 : Val), Keeps c P (iterCall srcs oracle tgt 0 x0 x1 x2) fun _ => True := by
  have := call_zero (c := c) (P := P) (srcs := srcs) (oracle := oracle) (tgt := tgt); intros; unfold iterCall; keeps

set_option maxHeartbeats 4000000 in
theorem eval_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Exp), Keeps c P (eval srcs oracle tgt (n + 1) cx x1) fun _ => True := by
  cases ih; intros; unfold eval; keeps

set_option maxHeartbeats 4000000 in
theorem evalMulti_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Exp), Keeps c P (evalMulti srcs oracle tgt (n + 1) cx x1) fun _ => True := by
  cases ih; intros; unfold evalMulti; keeps

set_option maxHeartbeats 4000000 in
theorem evalList_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List Exp), Keeps c P (evalList srcs oracle tgt (n + 1) cx x1) fun _ => True := by
  cases ih; intros; unfold evalList; keeps

set_option maxHeartbeats 4000000 in
theorem tableCons_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List Field), Keeps c P (tableCons srcs oracle tgt (n + 1) cx x1) fun _ => True := by
  cases ih; intros; unfold tableCons; keeps

set_option maxHeartbeats 4000000 in
theorem fields_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Nat) (x2 : List Field), Keeps c P (fields srcs oracle tgt (n + 1) cx x1 x2) fun _ => True := by
  cases ih; intros; unfold fields; keeps

set_option maxHeartbeats 4000000 in
theorem index_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Val) (x1 : Val), Keeps c P (index srcs oracle tgt (n + 1) x0 x1) fun _ => True := by
  cases ih; intros; unfold index; keeps

set_option maxHeartbeats 4000000 in
theorem cdMetaIndex_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : CType) (x1 : Val) (x2 : Val), Keeps c P (cdMetaIndex srcs oracle tgt (n + 1) x0 x1 x2) fun _ => True := by
  cases ih; intros; unfold cdMetaIndex; keeps

set_option maxHeartbeats 4000000 in
theorem cdMetaGet_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : CType) (x1 : Val) (x2 : Val), Keeps c P (cdMetaGet srcs oracle tgt (n + 1) x0 x1 x2) fun _ => True := by
  cases ih; intros; unfold cdMetaGet; keeps

set_option maxHeartbeats 4000000 in
theorem call_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Val) (x1 : List Val), Keeps c P (call srcs oracle tgt (n + 1) x0 x1) fun _ => True := by
  cases ih; intros; unfold call; keeps

set_option maxHeartbeats 4000000 in
theorem execBlock_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Block), Keeps c P (execBlock srcs oracle tgt (n + 1) cx x1) fun _ => True := by
  cases ih; intros; unfold execBlock; keeps

set_option maxHeartbeats 4000000 in
theorem execSeq_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Block) (x2 : Block) (x3 : Option Exp), Keeps c P (execSeq srcs oracle tgt (n + 1) cx x1 x2 x3) fun _ => True := by
  cases ih; intros; unfold execSeq; keeps

set_option maxHeartbeats 4000000 in
theorem execStat_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Stat), Keeps c P (execStat srcs oracle tgt (n + 1) cx x1) fun _ => True := by
  cases ih; intros; unfold execStat; keeps

set_option maxHeartbeats 4000000 in
theorem places_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List Exp), Keeps c P (places srcs oracle tgt (n + 1) cx x1) fun _ => True := by
  cases ih; intros; unfold places; keeps

set_option maxHeartbeats 4000000 in
theorem assign_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List (String ⊕ Val × Val × Option Site)) (x2 : List Val), Keeps c P (assign srcs oracle tgt (n + 1) cx x1 x2) fun _ => True := by
  cases ih; intros; unfold assign; keeps

set_option maxHeartbeats 4000000 in
theorem setindex_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Val) (x1 : Val) (x2 : Val), Keeps c P (setindex srcs oracle tgt (n + 1) x0 x1 x2) fun _ => True := by
  cases ih; intros; unfold setindex; keeps

set_option maxHeartbeats 4000000 in
theorem less_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Val) (x1 : Val) (x2 : Bool) (x3 : Option String), Keeps c P (less srcs oracle tgt (n + 1) x0 x1 x2 x3) fun _ => True := by
  cases ih; intros; unfold less; keeps

set_option maxHeartbeats 4000000 in
theorem eqv_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Val) (x1 : Val), Keeps c P (eqv srcs oracle tgt (n + 1) x0 x1) fun _ => True := by
  cases ih; intros; unfold eqv; keeps

set_option maxHeartbeats 4000000 in
theorem printArgs_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : List Val) (x1 : List Char) (x2 : Bool), Keeps c P (printArgs srcs oracle tgt (n + 1) x0 x1 x2) fun _ => True := by
  cases ih; intros; unfold printArgs; keeps

set_option maxHeartbeats 4000000 in
theorem unop_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : UnOp) (x1 : Val), Keeps c P (unop srcs oracle tgt (n + 1) x0 x1) fun _ => True := by
  cases ih; intros; unfold unop; keeps

set_option maxHeartbeats 4000000 in
theorem whileLoop_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Exp) (x2 : Block), Keeps c P (whileLoop srcs oracle tgt (n + 1) cx x1 x2) fun _ => True := by
  cases ih; intros; unfold whileLoop; keeps

set_option maxHeartbeats 4000000 in
theorem rptLoop_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : Block) (x2 : Exp), Keeps c P (rptLoop srcs oracle tgt (n + 1) cx x1 x2) fun _ => True := by
  cases ih; intros; unfold rptLoop; keeps

set_option maxHeartbeats 4000000 in
theorem numLoop_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : String) (x2 : Num) (x3 : Num) (x4 : Num) (x5 : Block), Keeps c P (numLoop srcs oracle tgt (n + 1) cx x1 x2 x3 x4 x5) fun _ => True := by
  cases ih; intros; unfold numLoop; keeps

set_option maxHeartbeats 4000000 in
theorem inLoop_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (cx : Ctx) (_ : EnvOk c cx.env) (x1 : List String) (x2 : Val) (x3 : Val) (x4 : Val) (x5 : Block), Keeps c P (inLoop srcs oracle tgt (n + 1) cx x1 x2 x3 x4 x5) fun _ => True := by
  cases ih; intros; unfold inLoop; keeps

set_option maxHeartbeats 4000000 in
theorem callPrim_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : String) (x1 : List Val) (x2 : List Val), Keeps c P (callPrim srcs oracle tgt (n + 1) x0 x1 x2) fun _ => True := by
  cases ih; intros; unfold callPrim; keeps

set_option maxHeartbeats 4000000 in
theorem readChunk_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Val) (x1 : List Char), Keeps c P (readChunk srcs oracle tgt (n + 1) x0 x1) fun _ => True := by
  cases ih; intros; unfold readChunk; keeps

set_option maxHeartbeats 4000000 in
theorem foreachi_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Int) (x3 : Int), Keeps c P (foreachi srcs oracle tgt (n + 1) x0 x1 x2 x3) fun _ => True := by
  cases ih; intros; unfold foreachi; keeps

set_option maxHeartbeats 4000000 in
theorem foreachK_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Val), Keeps c P (foreachK srcs oracle tgt (n + 1) x0 x1 x2) fun _ => True := by
  cases ih; intros; unfold foreachK; keeps

set_option maxHeartbeats 4000000 in
theorem lessThan_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Val) (x1 : Val) (x2 : Val), Keeps c P (lessThan srcs oracle tgt (n + 1) x0 x1 x2) fun _ => True := by
  cases ih; intros; unfold lessThan; keeps

set_option maxHeartbeats 4000000 in
theorem sortAux_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Int) (x3 : Int), Keeps c P (sortAux srcs oracle tgt (n + 1) x0 x1 x2 x3) fun _ => True := by
  cases ih; intros; unfold sortAux; keeps

set_option maxHeartbeats 4000000 in
theorem sortPart_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Val) (x3 : Int) (x4 : Int) (x5 : Int) (x6 : Int), Keeps c P (sortPart srcs oracle tgt (n + 1) x0 x1 x2 x3 x4 x5 x6) fun _ => True := by
  cases ih; intros; unfold sortPart; keeps

set_option maxHeartbeats 4000000 in
theorem sortUp_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Val) (x3 : Int) (x4 : Int), Keeps c P (sortUp srcs oracle tgt (n + 1) x0 x1 x2 x3 x4) fun _ => True := by
  cases ih; intros; unfold sortUp; keeps

set_option maxHeartbeats 4000000 in
theorem sortDown_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Nat) (x1 : Val) (x2 : Val) (x3 : Int) (x4 : Int), Keeps c P (sortDown srcs oracle tgt (n + 1) x0 x1 x2 x3 x4) fun _ => True := by
  cases ih; intros; unfold sortDown; keeps

set_option maxHeartbeats 4000000 in
theorem gsub_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : List Val), Keeps c P (gsub srcs oracle tgt (n + 1) x0) fun _ => True := by
  cases ih; intros; unfold gsub; keeps

set_option maxHeartbeats 4000000 in
theorem gsubGo_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Pat.MS) (x1 : Val) (x2 : Bool) (x3 : Int) (x4 : Nat) (x5 : Nat) (x6 : List Char), Keeps c P (gsubGo srcs oracle tgt (n + 1) x0 x1 x2 x3 x4 x5 x6) fun _ => True := by
  cases ih; intros; unfold gsubGo; keeps

set_option maxHeartbeats 4000000 in
theorem addValue_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Pat.MS) (x1 : Val) (x2 : Array Pat.Cap) (x3 : Nat) (x4 : Nat), Keeps c P (addValue srcs oracle tgt (n + 1) x0 x1 x2 x3 x4) fun _ => True := by
  cases ih; intros; unfold addValue; keeps

set_option maxHeartbeats 4000000 in
theorem binop_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : BinOp) (x1 : Val) (x2 : Val), Keeps c P (binop srcs oracle tgt (n + 1) x0 x1 x2) fun _ => True := by
  have := eqv_succ ih; have := less_succ ih; cases ih; intros; unfold binop; keeps

set_option maxHeartbeats 4000000 in
theorem iterCall_succ {n : Nat} (ih : AllK c P srcs oracle tgt n) :
    ∀ (x0 : Val) (x1 : Val) (x2 : Val), Keeps c P (iterCall srcs oracle tgt (n + 1) x0 x1 x2) fun _ => True := by
  have := call_succ ih; cases ih; intros; unfold iterCall; keeps

theorem allK : ∀ n, AllK c P srcs oracle tgt n
  | 0 => ⟨eval_zero, evalMulti_zero, evalList_zero, tableCons_zero, fields_zero, index_zero, cdMetaIndex_zero, cdMetaGet_zero, call_zero, execBlock_zero, execSeq_zero, execStat_zero, places_zero, assign_zero, setindex_zero, binop_zero, less_zero, eqv_zero, printArgs_zero, unop_zero, whileLoop_zero, rptLoop_zero, numLoop_zero, iterCall_zero, inLoop_zero, callPrim_zero, readChunk_zero, foreachi_zero, foreachK_zero, lessThan_zero, sortAux_zero, sortPart_zero, sortUp_zero, sortDown_zero, gsub_zero, gsubGo_zero, addValue_zero⟩
  | n + 1 => have ih := allK n; ⟨eval_succ ih, evalMulti_succ ih, evalList_succ ih, tableCons_succ ih, fields_succ ih, index_succ ih, cdMetaIndex_succ ih, cdMetaGet_succ ih, call_succ ih, execBlock_succ ih, execSeq_succ ih, execStat_succ ih, places_succ ih, assign_succ ih, setindex_succ ih, binop_succ ih, less_succ ih, eqv_succ ih, printArgs_succ ih, unop_succ ih, whileLoop_succ ih, rptLoop_succ ih, numLoop_succ ih, iterCall_succ ih, inLoop_succ ih, callPrim_succ ih, readChunk_succ ih, foreachi_succ ih, foreachK_succ ih, lessThan_succ ih, sortAux_succ ih, sortPart_succ ih, sortUp_succ ih, sortDown_succ ih, gsub_succ ih, gsubGo_succ ih, addValue_succ ih⟩

/-- the frame rule: a call, of any function and arguments at any fuel, keeps the caller's own cell `c` -/
theorem call_keeps {n : Nat} {f : Val} {args : List Val} :
    Keeps c P (call srcs oracle tgt n f args) fun _ => True := (allK n).call f args

end
/-! Where the frame rule starts: a fresh cell is own -/
section fresh
variable {P : Val → Prop}

/-- a heap whose fresh cell is own: its coroutines hold no heaps, its closures capture only cells it has -/
def Fresh (h : Heap) : Prop :=
  (∀ (a : Nat) (t : Thr Heap), h[a]? = some (Obj.thr t) → t.hist = [] ∧ t.script = []) ∧
  (∀ (a : Nat) (cl : Clo), h[a]? = some (Obj.clo cl) → ∀ x ∈ cl.env, x.2 < h.size)

theorem Fresh.push {h : Heap} {v : Val} (f : Fresh h) : Fresh (h.push (.cell v)) := by
  refine ⟨fun a t e => ?_, fun a cl e x hx => ?_⟩
  · rw [Array.getElem?_push] at e; split at e
    · cases e
    · exact f.1 a t e
  · rw [Array.getElem?_push] at e; split at e
    · cases e
    · have := f.2 a cl e x hx; simp only [Array.size_push]; omega

theorem Own.fresh {h : Heap} {v : Val} (f : Fresh h) (hs : 16 < h.size) (p : P v) :
    Own h.size P (h.push (.cell v)) := by
  refine .intro ⟨v, by simp, p⟩ hs (fun a cl e x hx => ?_) (fun a t e x hx => ?_)
  · rw [Array.getElem?_push] at e; split at e
    · cases e
    · exact Nat.ne_of_lt (f.2 a cl e x hx)
  · rw [Array.getElem?_push] at e; split at e
    · cases e
    · obtain ⟨h1, h2⟩ := f.1 a t e; simp [h1, h2] at hx

/-- a write of its own cell, of a value with `P` -/
theorem Own.setSelf {c : Nat} {h : Heap} {v : Val} (o : Own c P h) (p : P v) : Own c P (h.set! c (.cell v)) := by
  have lt := o.lt
  cases o with
  | intro cell sys hc ht =>
  have get : ∀ b, (h.set! c (.cell v))[b]? = if c = b ∧ c < h.size then some (.cell v) else h[b]? := by
    intro b; simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]; split <;> simp_all
  refine .intro ⟨v, by rw [get]; simp [lt], p⟩ sys (fun b cl e => ?_) (fun b t e => ?_)
  · rw [get] at e; split at e
    · cases e
    · exact hc _ _ e
  · rw [get] at e; split at e
    · cases e
    · exact ht _ _ e

end fresh

end Lua
