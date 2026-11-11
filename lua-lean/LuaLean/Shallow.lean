import LuaLean.Interp

/-! The target of the Lua→Lean translator (`tools/Lift.lean`), as AutoCorres's first two stages are for C: a shallow
embedding in the interpreter's monad `M`, one combinator per clause of `Interp.lean`, and one lemma per combinator
saying it is that clause. The translator writes each Lua function as a term of these combinators
with no syntax tree left in it but the bodies of the closures it creates, and every local resolved: a local is the
Lean variable naming its cell, a global is `_G`'s field. That the shallow function is the interpreter's run of the
parsed function for every fuel is `D.fn_ok` (`Denote.lean`), a proof made of the lemmas below.

Fuel is threaded as the interpreter threads it (`tick`), so the two are equal, not just alike, and the heap is the
same heap: the shallow code allocates the same cells. -/

namespace Lua

/-- one unit of fuel, as each clause of the interpreter takes it -/
def tick {α} (n : Nat) (k : Nat → M α) : M α :=
  match n with
  | 0 => throw .fuel
  | n + 1 => k n

/-- the interpreter's parameters: the modules given as source, the oracle for effects, and the LuaJIT build -/
structure Sem where
  srcs : String → Option Block
  oracle : Oracle
  tgt : Target

/-- what calling a closure does, once its address has been read (`call`'s `.fn` clause) -/
def callClo (I : Sem) (n : Nat) (c : Clo) (args : List Val) : M (List Val) := frame do
  let cx ← bindLocals ⟨c.env, []⟩ c.params args
  let cx := { cx with va := if c.va then args.drop c.params.length else [] }
  match ← execBlock I.srcs I.oracle I.tgt n cx c.body with
  | .ret vs => pure vs
  | .norm => pure []
  | .brk => die "break outside a loop"
  | .goto l => die s!"no visible label '{l}' for goto"

theorem call_fn (I : Sem) (n a : Nat) (args : List Val) (h : Heap) (c : Clo) (ha : h[a]? = some (.clo c)) :
    call I.srcs I.oracle I.tgt (n + 1) (.fn a) args h = callClo I n c args h := by
  rw [call]; simp only [bind, EStateM.bind, getObj, get, getThe, MonadStateOf.get, EStateM.get, ha]; rfl

/-! What a call into a builtin or the world is: a spec of a lifted function unfolds its calls with these. -/

theorem call_prim (I : Sem) (n : Nat) (name : String) (bound args : List Val) :
    call I.srcs I.oracle I.tgt (n + 1) (.prim name bound) args =
      frame (callPrim I.srcs I.oracle I.tgt n name bound args) := by
  rw [call]

theorem call_eff (I : Sem) (n : Nat) (name : String) (args : List Val) :
    call I.srcs I.oracle I.tgt (n + 1) (.eff name) args = effect I.oracle name args := by
  rw [call]

/-- print of strings and numbers: no `__tostring` to call, one write -/
theorem callPrim_print (I : Sem) (n : Nat) (args : List Val)
    (hs : args.all fun v => match v with | .str _ | .num _ => true | _ => false) :
    callPrim I.srcs I.oracle I.tgt (n + 1) "print" [] args = printFn I.oracle args := by
  have any : ∀ h, (args.anyM (m := M) fun v => do pure !(← metaOf v "__tostring").isNil) h = .ok false h := by
    intro h
    induction args with
    | nil => rfl
    | cons v vs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hs
      obtain ⟨hv, hs⟩ := hs
      have ih := ih hs
      cases v <;> simp at hv <;> simp only [List.anyM, metaOf, bind, EStateM.bind, pure, EStateM.pure, Val.isNil] at ih ⊢ <;>
        simpa using ih
  rw [callPrim]; funext h; simp only [bind, EStateM.bind] at any ⊢; simp [any]

theorem callPrim_write (I : Sem) (n : Nat) (args : List Val) :
    callPrim I.srcs I.oracle I.tgt (n + 1) "io.write" [] args = ioWrite I.oracle args := by
  rw [callPrim]

theorem callPrim_date (I : Sem) (n : Nat) (args : List Val) :
    callPrim I.srcs I.oracle I.tgt (n + 1) "os.date" [] args = osDate I.oracle args := by
  rw [callPrim]

/-- `os.time()`: the clock -/
theorem callPrim_time (I : Sem) (n : Nat) :
    callPrim I.srcs I.oracle I.tgt (n + 1) "os.time" [] [] = (do pure [timeVal (← timeFx I.oracle "os.time" [])]) := by
  rw [callPrim]; rfl

/-- the debug library's modelled functions -/
theorem callPrim_debug (I : Sem) (n : Nat) (name : String) (args : List Val)
    (hn : name = "debug.getmetatable" ∨ name = "debug.setmetatable" ∨ name = "debug.getupvalue" ∨
      name = "debug.setupvalue" ∨ name = "debug.getinfo" ∨ name = "debug.traceback") :
    callPrim I.srcs I.oracle I.tgt (n + 1) name [] args = debugFn name args := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [callPrim, basicFn] <;> simp

/-- the bit library's functions -/
theorem callPrim_bit (I : Sem) (n : Nat) (name : String) (args : List Val) (hn : name ∈ bits.map ("bit." ++ ·)) :
    callPrim I.srcs I.oracle I.tgt (n + 1) name [] args = bitFn name args := by
  simp only [bits, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, String.reduceAppend] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [callPrim, basicFn] <;>
    simp

/-- an assignment target as the shallow code writes it: given the fuel of the assignment, a value to write -/
abbrev W := Nat → Val → M Unit

/-- a table's field, through `__newindex`, its errors reported at `s` -/
def wtbl (I : Sem) (s : Option Site) (tv kv : Val) : W := fun n v => atSite? s (setindex I.srcs I.oracle I.tgt n tv kv v)

def writer (I : Sem) (cx : Ctx) : String ⊕ (Val × Val × Option Site) → W
  | .inl x => fun _ => setVar cx x
  | .inr (tv, kv, s) => wtbl I s tv kv

/-- `assign`, with each target a writer -/
def assignW : Nat → List W → List Val → M Unit
  | 0, _, _ => throw .fuel
  | _ + 1, [], _ => pure ()
  | n + 1, w :: ws, vs => do w n (vs.headD .nil); assignW n ws vs.tail

theorem assign_writers (I : Sem) (n : Nat) (cx : Ctx) (ps : List (String ⊕ (Val × Val × Option Site))) (vs : List Val) :
    assign I.srcs I.oracle I.tgt n cx ps vs = assignW n (ps.map (writer I cx)) vs := by
  induction n generalizing ps vs with
  | zero => rw [assign]; rfl
  | succ n ih =>
    rcases ps with _ | ⟨p, ps⟩
    · rw [assign]; rfl
    · rw [assign.eq_def]; simp only [List.map_cons, assignW, ← ih]
      rcases p with x | ⟨tv, kv, s⟩ <;> rfl

/-- the labels ending a block, and all its labels: what a `goto` out of one of its statements does -/
def trail (b : Block) : List String :=
  (b.reverse.takeWhile fun s => match s with | .label _ => true | _ => false).filterMap
    fun s => match s with | .label x => some x | _ => none
def labels (b : Block) : List String := b.filterMap fun s => match s with | .label x => some x | _ => none

/-- `local` and `local function`, which `execSeq` runs itself -/
def Stat.isDecl : Stat → Bool
  | .loc .. | .locfn .. => true
  | _ => false

namespace S

abbrev SE := Nat → M Val
abbrev SM := Nat → M (List Val)
abbrev SB := Nat → M Flow

-- ---------- expressions ----------
def eNil : SE := fun n => tick n fun _ => pure .nil
def eTrue : SE := fun n => tick n fun _ => pure (.bool true)
def eFalse : SE := fun n => tick n fun _ => pure (.bool false)
def eNum (x : Num) : SE := fun n => tick n fun _ => pure (.num x)
def eStr (s : List Char) : SE := fun n => tick n fun _ => pure (.str s)
def eVa (va : List Val) : SE := fun n => tick n fun _ => pure (va.headD .nil)
/-- a closure: its body is data, and `env` the scope it closes over -/
def eFunc (ps : List String) (va : Bool) (b : Block) (env : Env) : SE :=
  fun n => tick n fun _ => do pure (.fn (← alloc (.clo ⟨ps, va, b, env⟩)))
/-- a local, by its cell -/
def eCell (c : Nat) : SE := fun n => tick n fun _ => readCell c
/-- a global -/
def eGlob (x : String) : SE := fun n => tick n fun _ => rawget G (lstr x)
def eIndex (I : Sem) (t k : SE) : SE := fun n => tick n fun n => do
  let tv ← t n
  let kv ← k n
  index I.srcs I.oracle I.tgt n tv kv
/-- `e`, its errors reported at `s` -/
def eSite (s : Site) (e : SE) : SE := fun n => tick n fun n => atSite s (e n)
/-- a call's first value -/
def eFirst (m : SM) : SE := fun n => tick n fun n => do pure ((← m n).headD .nil)
def eParen (e : SE) : SE := fun n => tick n fun n => e n
def eAnd (a b : SE) : SE := fun n => tick n fun n => do
  let x ← a n
  if x.truthy then b n else pure x
def eOr (a b : SE) : SE := fun n => tick n fun n => do
  let x ← a n
  if x.truthy then pure x else b n
def eUn (I : Sem) (op : UnOp) (a : SE) : SE := fun n => tick n fun n => do
  unop I.srcs I.oracle I.tgt n op (← a n)
def eBin (I : Sem) (op : BinOp) (a b : SE) : SE := fun n => tick n fun n => do
  let x ← a n
  let y ← b n
  binop I.srcs I.oracle I.tgt n op x y
/-- a table constructor: `fs` the fields, given the new table's address -/
def eTable (fs : Nat → SM) : SE := fun n => tick n fun n => tick n fun n => do
  let t ← alloc (.tbl {})
  let pos ← fs t n
  let mut i : Int := 1
  for v in pos do
    rawset t (nums i) v
    i := i + 1
  pure (.tbl t)

-- ---------- several values ----------
def mCall (I : Sem) (f : SE) (as : SM) : SM := fun n => tick n fun n => do
  let fv ← f n
  let as ← as n
  call I.srcs I.oracle I.tgt n fv as
def mMethod (I : Sem) (o : SE) (m : String) (as : SM) : SM := fun n => tick n fun n => do
  let ov ← o n
  let fv ← index I.srcs I.oracle I.tgt n ov (.str m.toList)
  let as ← as n
  call I.srcs I.oracle I.tgt n fv (ov :: as)
def mSite (s : Site) (m : SM) : SM := fun n => tick n fun n => atSite s (m n)
def mVa (va : List Val) : SM := fun n => tick n fun _ => pure va
def mOne (e : SE) : SM := fun n => tick n fun n => do pure [← e n]

def lNil : SM := fun n => tick n fun _ => pure []
def lLast (m : SM) : SM := fun n => tick n fun n => m n
def lCons (e : SE) (l : SM) : SM := fun n => tick n fun n => do
  let v ← e n
  let vs ← l n
  pure (v :: vs)

-- ---------- table fields, given the table ----------
def fNil : Nat → SM := fun _ n => tick n fun _ => pure []
def fLast (m : SM) : Nat → SM := fun _ n => tick n fun n => m n
def fPos (e : SE) (fs : Nat → SM) : Nat → SM := fun t n => tick n fun n => do
  let v ← e n
  let vs ← fs t n
  pure (v :: vs)
def fNamed (k : String) (e : SE) (fs : Nat → SM) : Nat → SM := fun t n => tick n fun n => do
  let v ← e n
  rawset t (lstr k) v
  fs t n
def fKeyed (k e : SE) (fs : Nat → SM) : Nat → SM := fun t n => tick n fun n => do
  let kv ← k n
  let v ← e n
  rawset t kv v
  fs t n

-- ---------- assignment targets, as writers ----------
abbrev SP := Nat → M (List W)
def pNil : SP := fun n => tick n fun _ => pure []
def pVar (w : W) (ps : SP) : SP := fun n => tick n fun n => do pure (w :: (← ps n))
/-- a table's field, `s` where its errors are reported -/
def pIndex (I : Sem) (s : Option Site) (t k : SE) (ps : SP) : SP := fun n => tick n fun n => do
  let tv ← t n
  let kv ← k n
  pure (wtbl I s tv kv :: (← ps n))
/-- a local's cell, or a global -/
def wCell (c : Nat) : W := fun _ => writeCell c
def wGlob (x : String) : W := fun _ => rawset G (lstr x)

-- ---------- statements ----------
def sAssign (ps : SP) (es : SM) : SB := fun n => tick n fun n => do
  let ws ← ps n
  let vs ← es n
  assignW n ws.reverse (vs ++ List.replicate ws.length Val.nil |>.take ws.length).reverse
  pure .norm
def sCall (m : SM) : SB := fun n => tick n fun n => do let _ ← m n; pure .norm
def sBlock (b : SB) : SB := fun n => tick n fun n => b n
def whileL (c : SE) (b : SB) : Nat → M Flow
  | 0 => throw .fuel
  | n + 1 => do
    if !(← c n).truthy then return .norm
    match ← b n with
    | .norm => whileL c b n
    | .brk => pure .norm
    | fl => pure fl
def sWhile (c : SE) (b : SB) : SB := fun n => tick n fun n => whileL c b n
def rptL (b : SB) : Nat → M Flow
  | 0 => throw .fuel
  | n + 1 => do
    match ← b n with
    | .norm => rptL b n
    | .brk => pure .norm
    | fl => pure fl
/-- `b` is the body with the condition at its end (`qEndRpt`) -/
def sRepeat (b : SB) : SB := fun n => tick n fun n => rptL b n
def sIf (c : SE) (t e : SB) : SB := fun n => tick n fun n => do
  if (← c n).truthy then t n else e n
/-- `body c`: the body with the loop variable in cell `c` -/
def numL (body : Nat → SB) : Nat → Num → Num → Num → M Flow
  | 0, _, _, _ => throw .fuel
  | n + 1, i, lim, st => do
    if !(if (Num.int 0).lt st then i.le lim else lim.le i) then return .norm
    let c ← alloc (.cell (.num i))
    match ← body c n with
    | .norm => numL body n (i.add st) lim st
    | .brk => pure .norm
    | fl => pure fl
def forNum (x : Val) (what : String) : M Num := match x.toNum with
  | some x => pure x
  | none => rtErr s!"'for' {what} must be a number"
def sForNum (a b : SE) (st : Option SE) (body : Nat → SB) : SB := fun n => tick n fun n => do
  let a ← forNum (← a n) "initial value"
  let b ← forNum (← b n) "limit"
  let st ← match st with
    | some st => do forNum (← st n) "step"
    | none => pure (.int 1)
  match a, b, st with
  | .int _, .int _, .int _ => numL body n a b st
  | _, _, _ => numL body n (.flt a.toFloat) (.flt b.toFloat) (.flt st.toFloat)
/-- `body n rs`: the body at fuel `n` with the loop variables bound to `rs` -/
def inL (I : Sem) (body : Nat → List Val → M Flow) : Nat → Val → Val → Val → M Flow
  | 0, _, _, _ => throw .fuel
  | n + 1, f, s, ctl => do
    let rs ← iterCall I.srcs I.oracle I.tgt n f s ctl
    let v1 := rs.headD .nil
    if v1.isNil then return .norm
    match ← body n rs with
    | .norm => inL I body n f s v1
    | .brk => pure .norm
    | fl => pure fl
def sForIn (I : Sem) (es : SM) (body : Nat → List Val → M Flow) : SB := fun n => tick n fun n => do
  let r ← es n
  inL I body n (r.getD 0 .nil) (r.getD 1 .nil) (r.getD 2 .nil)
def sReturn (es : SM) : SB := fun n => tick n fun n => do pure (.ret (← es n))
def sSite (s : Site) (b : SB) : SB := fun n => tick n fun n => atSite s (b n)
def sBreak : SB := fun n => tick n fun _ => pure .brk
def sGoto (l : String) : SB := fun n => tick n fun _ => pure (.goto l)
def sLabel : SB := fun n => tick n fun _ => pure .norm

-- ---------- blocks ----------
/-- a block: its statements, from the first -/
def block (q : SB) : SB := fun n => tick n fun n => q n
def qEnd : SB := fun n => tick n fun _ => pure .norm
/-- the end of a repeat's body: its condition -/
def qEndRpt (c : SE) : SB := fun n => tick n fun n => do pure (if (← c n).truthy then .brk else .norm)
/-- `local x, y = es`: `k n` binds the values (`let1`, then `letEnd`) and runs the rest at fuel `n` -/
def qLocal (es : SM) (k : Nat → List Val → M Flow) : SB := fun n => tick n fun n => do
  let vs ← es n
  k n vs
def let1 {α} (k : Nat → List Val → M α) : List Val → M α := fun vs => do
  let c ← alloc (.cell (vs.headD .nil))
  k c vs.tail
def letEnd {α} (x : M α) : List Val → M α := fun _ => x
/-- `local function name`: its cell is in scope in its body and in `k`, the rest -/
def qLocalFn (name : String) (ps : List String) (va : Bool) (b : Block) (env : Env) (k : Nat → SB) : SB :=
  fun n => tick n fun n => do
    let c ← alloc (.cell .nil)
    let f ← alloc (.clo ⟨ps, va, b, (name, c) :: env⟩)
    writeCell c (.fn f)
    k c n
/-- a goto out of a statement: to a label ending the block (`ends`) it ends the block, to another of the block's
labels (`all`) the run stops (outside the subset), else it leaves the block -/
def gotos (ends all : List String) (l : String) : M Flow :=
  if ends.contains l then pure .norm
  else if all.contains l then throw (.eff "goto: a label that does not end its block" [])
  else pure (.goto l)
/-- a statement, then the rest `q` -/
def qStat (s : SB) (g : String → M Flow) (q : SB) : SB := fun n => tick n fun n => do
  match ← s n with
  | .norm => q n
  | .goto l => g l
  | fl => pure fl

/-- a function: `k args n` binds the parameters to `args` and runs the body at fuel `n` -/
def fn (k : List Val → Nat → List Val → M Flow) : List Val → Nat → M (List Val) := fun args n => frame do
  match ← k args n args with
  | .ret vs => pure vs
  | .norm => pure []
  | .brk => die "break outside a loop"
  | .goto l => die s!"no visible label '{l}' for goto"

end S

-- ---------- what each combinator is ----------

section
variable (I : Sem)
open S

abbrev CE (s : SE) (cx : Ctx) (e : Exp) : Prop := ∀ n, s n = eval I.srcs I.oracle I.tgt n cx e
abbrev CM (s : SM) (cx : Ctx) (e : Exp) : Prop := ∀ n, s n = evalMulti I.srcs I.oracle I.tgt n cx e
abbrev CL (s : SM) (cx : Ctx) (es : List Exp) : Prop := ∀ n, s n = evalList I.srcs I.oracle I.tgt n cx es
abbrev CF (s : Nat → SM) (cx : Ctx) (fs : List Field) : Prop := ∀ t n, s t n = fields I.srcs I.oracle I.tgt n cx t fs
abbrev CP (s : SP) (cx : Ctx) (ts : List Exp) : Prop :=
  ∀ n, s n = (fun ps => ps.map (writer I cx)) <$> places I.srcs I.oracle I.tgt n cx ts
abbrev CS (s : SB) (cx : Ctx) (st : Stat) : Prop := ∀ n, s n = execStat I.srcs I.oracle I.tgt n cx st
abbrev CK (s : SB) (cx : Ctx) (b : Block) : Prop := ∀ n, s n = execBlock I.srcs I.oracle I.tgt n cx b
abbrev CQ (s : SB) (cx : Ctx) (full rest : Block) (fin : Option Exp) : Prop :=
  ∀ n, s n = execSeq I.srcs I.oracle I.tgt n cx full rest fin
/-- a chain of `bind`s: binding `names` to the values, then `K` -/
abbrev CBs {α} (k : List Val → M α) (cx : Ctx) (names : List String) (K : Ctx → M α) : Prop :=
  ∀ vs, k vs = bindLocals cx names vs >>= K
abbrev CFn (s : List Val → Nat → M (List Val)) (c : Clo) : Prop := ∀ args n, s args n = callClo I n c args

variable {I}

-- expressions
theorem CE_nil {cx} : CE I eNil cx .nil := by intro n; cases n <;> rw [eval] <;> rfl
theorem CE_true {cx} : CE I eTrue cx .tru := by intro n; cases n <;> rw [eval] <;> rfl
theorem CE_false {cx} : CE I eFalse cx .fls := by intro n; cases n <;> rw [eval] <;> rfl
theorem CE_num {cx x} : CE I (eNum x) cx (.num x) := by intro n; cases n <;> rw [eval] <;> rfl
theorem CE_str {cx s} : CE I (eStr s) cx (.str s) := by intro n; cases n <;> rw [eval] <;> rfl
theorem CE_va {cx va} (h : va = cx.va) : CE I (eVa va) cx .vararg := by subst h; intro n; cases n <;> rw [eval] <;> rfl
theorem CE_func {cx ps va b env} (h : env = cx.env) : CE I (eFunc ps va b env) cx (.func ps va b) := by
  subst h; intro n; cases n <;> rw [eval] <;> rfl
theorem CE_cell {cx x c} (h : cx.env.lookup x = some c) : CE I (eCell c) cx (.var x) := by
  intro n; cases n <;> rw [eval] <;> simp [eCell, tick, getVar, h]
theorem CE_glob {cx x} (h : cx.env.lookup x = none) : CE I (eGlob x) cx (.var x) := by
  intro n; cases n <;> rw [eval] <;> simp [eGlob, tick, getVar, h]
theorem CE_index {cx t k st sk} (ht : CE I st cx t) (hk : CE I sk cx k) : CE I (eIndex I st sk) cx (.index t k) := by
  intro n; cases n <;> rw [eval] <;> simp [eIndex, tick, ht, hk]
theorem CE_call {cx f as m} (h : CM I m cx (.call f as)) : CE I (eFirst m) cx (.call f as) := by
  intro n; cases n <;> rw [eval] <;> simp [eFirst, tick, h]
theorem CE_method {cx o x as m} (h : CM I m cx (.method o x as)) : CE I (eFirst m) cx (.method o x as) := by
  intro n; cases n <;> rw [eval] <;> simp [eFirst, tick, h]
theorem CE_paren {cx e s} (h : CE I s cx e) : CE I (eParen s) cx (.paren e) := by
  intro n; cases n <;> rw [eval] <;> simp [eParen, tick, h]
theorem CE_site {cx st e s} (h : CE I s cx e) : CE I (eSite st s) cx (.site st e) := by
  intro n; cases n <;> rw [eval] <;> simp [eSite, tick, h]
theorem CE_and {cx a b sa sb} (ha : CE I sa cx a) (hb : CE I sb cx b) : CE I (eAnd sa sb) cx (.and a b) := by
  intro n; cases n <;> rw [eval] <;> simp [eAnd, tick, ha, hb]
theorem CE_or {cx a b sa sb} (ha : CE I sa cx a) (hb : CE I sb cx b) : CE I (eOr sa sb) cx (.or a b) := by
  intro n; cases n <;> rw [eval] <;> simp [eOr, tick, ha, hb]
theorem CE_un {cx op a sa} (ha : CE I sa cx a) : CE I (eUn I op sa) cx (.un op a) := by
  intro n; cases n <;> rw [eval] <;> simp [eUn, tick, ha]
theorem CE_bin {cx op a b sa sb} (ha : CE I sa cx a) (hb : CE I sb cx b) : CE I (eBin I op sa sb) cx (.bin op a b) := by
  intro n; cases n <;> rw [eval] <;> simp [eBin, tick, ha, hb]
theorem CE_table {cx fs s} (h : CF I s cx fs) : CE I (eTable s) cx (.table fs) := by
  intro n; cases n with
  | zero => rw [eval]; rfl
  | succ n => rw [eval]; cases n <;> rw [tableCons] <;> simp [eTable, tick, h] <;> rfl

-- several values
theorem CM_call {cx f as sf sl} (hf : CE I sf cx f) (hl : CL I sl cx as) : CM I (mCall I sf sl) cx (.call f as) := by
  intro n; cases n <;> rw [evalMulti] <;> simp [mCall, tick, hf, hl]
theorem CM_method {cx o m as so sl} (ho : CE I so cx o) (hl : CL I sl cx as) :
    CM I (mMethod I so m sl) cx (.method o m as) := by
  intro n; cases n <;> rw [evalMulti] <;> simp [mMethod, tick, ho, hl]
theorem CM_va {cx va} (h : va = cx.va) : CM I (mVa va) cx .vararg := by subst h; intro n; cases n <;> rw [evalMulti] <;> rfl
theorem CM_site {cx st e m} (h : CM I m cx e) : CM I (mSite st m) cx (.site st e) := by
  intro n; cases n <;> rw [evalMulti] <;> simp [mSite, tick, h]
/-- an expression of one value: not a call, a method call or `...` -/
def Exp.single : Exp → Bool
  | .call .. | .method .. | .vararg | .site .. => false
  | _ => true
theorem CM_one {cx e s} (he : e.single = true) (h : CE I s cx e) : CM I (mOne s) cx e := by
  intro n; cases n with
  | zero => rw [evalMulti]; rfl
  | succ n => cases e <;> simp_all [Exp.single, evalMulti, mOne, tick]

theorem CL_nil {cx} : CL I lNil cx [] := by intro n; cases n <;> rw [evalList] <;> rfl
theorem CL_last {cx e m} (h : CM I m cx e) : CL I (lLast m) cx [e] := by
  intro n; cases n <;> rw [evalList] <;> simp [lLast, tick, h]
theorem CL_cons {cx e e' es s l} (he : CE I s cx e) (hl : CL I l cx (e' :: es)) : CL I (lCons s l) cx (e :: e' :: es) := by
  intro n; cases n <;> rw [evalList] <;> simp [lCons, tick, he, hl]

-- fields
theorem CF_nil {cx} : CF I fNil cx [] := by intro t n; cases n <;> rw [fields] <;> rfl
theorem CF_last {cx e m} (h : CM I m cx e) : CF I (fLast m) cx [.pos e] := by
  intro t n; cases n <;> rw [fields] <;> simp [fLast, tick, h]
theorem CF_pos {cx e f fs s r} (he : CE I s cx e) (hr : CF I r cx (f :: fs)) : CF I (fPos s r) cx (.pos e :: f :: fs) := by
  intro t n; cases n <;> rw [fields] <;> simp [fPos, tick, he, hr]
theorem CF_named {cx k e fs s r} (he : CE I s cx e) (hr : CF I r cx fs) : CF I (fNamed k s r) cx (.named k e :: fs) := by
  intro t n; cases n <;> rw [fields] <;> simp [fNamed, tick, he, hr]
theorem CF_keyed {cx k e fs sk s r} (hk : CE I sk cx k) (he : CE I s cx e) (hr : CF I r cx fs) :
    CF I (fKeyed sk s r) cx (.keyed k e :: fs) := by
  intro t n; cases n <;> rw [fields] <;> simp [fKeyed, tick, hk, he, hr]

-- assignment targets
theorem wCell_ok {cx x c} (h : cx.env.lookup x = some c) : wCell c = fun _ => setVar cx x := by
  funext _ v; simp [wCell, setVar, h]
theorem wGlob_ok {cx x} (h : cx.env.lookup x = none) : wGlob x = fun _ => setVar cx x := by
  funext _ v; simp [wGlob, setVar, h]
theorem CP_nil {cx} : CP I pNil cx [] := by intro n; cases n <;> rw [places] <;> rfl
theorem CP_var {cx x ts w ps} (hw : w = fun _ => setVar cx x) (hp : CP I ps cx ts) :
    CP I (pVar w ps) cx (.var x :: ts) := by
  intro n; cases n with
  | zero => rw [places]; rfl
  | succ n => rw [places]; simp [pVar, tick, hp, hw, writer]
theorem CP_index {cx t k ts st sk ps} (ht : CE I st cx t) (hk : CE I sk cx k) (hp : CP I ps cx ts) :
    CP I (pIndex I none st sk ps) cx (.index t k :: ts) := by
  intro n; cases n with
  | zero => rw [places]; rfl
  | succ n => rw [places]; simp [pIndex, tick, ht, hk, hp, writer]
theorem CP_site {cx s t k ts st sk ps} (ht : CE I st cx t) (hk : CE I sk cx k) (hp : CP I ps cx ts) :
    CP I (pIndex I (some s) st sk ps) cx (.site s (.index t k) :: ts) := by
  intro n; cases n with
  | zero => rw [places]; rfl
  | succ n => rw [places]; simp [pIndex, tick, ht, hk, hp, writer]

-- statements
theorem CS_assign {cx ts es ps sl} (hp : CP I ps cx ts) (hl : CL I sl cx es) : CS I (sAssign ps sl) cx (.assign ts es) := by
  intro n; cases n with
  | zero => rw [execStat]; rfl
  | succ n =>
    rw [execStat]; simp only [sAssign, tick, hp, hl, assign_writers, map_eq_pure_bind, bind_assoc, pure_bind,
      List.length_map, List.map_reverse]
theorem CS_call {cx e m} (h : CM I m cx e) : CS I (sCall m) cx (.call e) := by
  intro n; cases n <;> rw [execStat] <;> simp [sCall, tick, h]
theorem CS_block {cx b s} (h : CK I s cx b) : CS I (sBlock s) cx (.block b) := by
  intro n; cases n <;> rw [execStat] <;> simp [sBlock, tick, h]
theorem whileL_ok {cx c b sc sb} (hc : CE I sc cx c) (hb : CK I sb cx b) :
    ∀ n, whileL sc sb n = whileLoop I.srcs I.oracle I.tgt n cx c b := by
  intro n; induction n with
  | zero => rw [whileLoop]; rfl
  | succ n ih => rw [whileLoop, whileL, hc, hb]; simp only [ih]; rfl
theorem CS_while {cx c b sc sb} (hc : CE I sc cx c) (hb : CK I sb cx b) : CS I (sWhile sc sb) cx (.while c b) := by
  intro n; cases n <;> rw [execStat] <;> simp [sWhile, tick, whileL_ok hc hb]
theorem rptL_ok {cx b c sb} (hb : CQ I sb cx b b (some c)) :
    ∀ n, rptL sb n = rptLoop I.srcs I.oracle I.tgt n cx b c := by
  intro n; induction n with
  | zero => rw [rptLoop]; rfl
  | succ n ih => rw [rptLoop, rptL, hb]; simp only [ih]; rfl
theorem CS_repeat {cx b c sb} (hb : CQ I sb cx b b (some c)) : CS I (sRepeat sb) cx (.rpt b c) := by
  intro n; cases n <;> rw [execStat] <;> simp [sRepeat, tick, rptL_ok hb]
theorem CS_if {cx c t e sc st se} (hc : CE I sc cx c) (ht : CK I st cx t) (he : CK I se cx e) :
    CS I (sIf sc st se) cx (.ite c t e) := by
  intro n; cases n <;> rw [execStat] <;> simp [sIf, tick, hc, ht, he]
theorem numL_ok {cx v body sb} (hb : ∀ c, CK I (sb c) { cx with env := (v, c) :: cx.env } body) :
    ∀ n i lim st, numL sb n i lim st = numLoop I.srcs I.oracle I.tgt n cx v i lim st body := by
  intro n; induction n with
  | zero => intro i lim st; rw [numLoop]; rfl
  | succ n ih =>
    intro i lim st; rw [numLoop, numL]; simp only [bindLocals, hb, ih, bind_assoc, pure_bind]; rfl
theorem CS_fornum {cx v a b st body sa sb sst sbody}
    (ha : CE I sa cx a) (hb : CE I sb cx b)
    (hst : match st, sst with | some e, some s => CE I s cx e | none, none => True | _, _ => False)
    (hbody : ∀ c, CK I (sbody c) { cx with env := (v, c) :: cx.env } body) :
    CS I (sForNum sa sb sst sbody) cx (.fornum v a b st body) := by
  intro n; cases n with
  | zero => rw [execStat]; rfl
  | succ n =>
    rw [execStat]
    rcases st with _ | e <;> rcases sst with _ | s <;> simp only at hst
    · simp only [sForNum, tick, ha, hb, numL_ok hbody]; rfl
    · simp only [sForNum, tick, ha, hb, hst, numL_ok hbody]; rfl
theorem inL_ok {cx vs body sbody}
    (hb : ∀ n, CBs (sbody n) cx vs (fun cx' => execBlock I.srcs I.oracle I.tgt n cx' body)) :
    ∀ n f s ctl, inL I sbody n f s ctl = inLoop I.srcs I.oracle I.tgt n cx vs f s ctl body := by
  intro n; induction n with
  | zero => intro f s ctl; rw [inLoop]; rfl
  | succ n ih => intro f s ctl; rw [inLoop, inL]; simp only [hb, ih, bind_assoc]; rfl
theorem CS_forin {cx vs es body sl sbody} (hl : CL I sl cx es)
    (hb : ∀ n, CBs (sbody n) cx vs (fun cx' => execBlock I.srcs I.oracle I.tgt n cx' body)) :
    CS I (sForIn I sl sbody) cx (.forin vs es body) := by
  intro n; cases n <;> rw [execStat] <;> simp [sForIn, tick, hl, inL_ok hb]
theorem CS_return {cx es s} (h : CL I s cx es) : CS I (sReturn s) cx (.ret es) := by
  intro n; cases n <;> rw [execStat] <;> simp [sReturn, tick, h]
theorem CS_break {cx} : CS I sBreak cx .brk := by intro n; cases n <;> rw [execStat] <;> rfl
theorem CS_goto {cx l} : CS I (sGoto l) cx (.goto l) := by intro n; cases n <;> rw [execStat] <;> rfl
theorem CS_label {cx l} : CS I sLabel cx (.label l) := by intro n; cases n <;> rw [execStat] <;> rfl
theorem CS_site {cx st s b} (h : CS I b cx s) : CS I (sSite st b) cx (.site st s) := by
  intro n; cases n <;> rw [execStat] <;> simp [sSite, tick, h]

-- blocks
theorem CK_block {cx b q} (h : CQ I q cx b b none) : CK I (block q) cx b := by
  intro n; cases n <;> rw [execBlock] <;> simp [block, tick, h]
theorem CQ_end {cx full} : CQ I qEnd cx full [] none := by intro n; cases n <;> rw [execSeq] <;> rfl
theorem CQ_endRpt {cx full c s} (h : CE I s cx c) : CQ I (qEndRpt s) cx full [] (some c) := by
  intro n; cases n <;> rw [execSeq] <;> simp [qEndRpt, tick, h]
theorem CQ_local {cx full names es rest fin sl k} (hl : CL I sl cx es)
    (hk : ∀ n, CBs (k n) cx names (fun cx' => execSeq I.srcs I.oracle I.tgt n cx' full rest fin)) :
    CQ I (qLocal sl k) cx full (.loc names es :: rest) fin := by
  intro n; cases n <;> rw [execSeq] <;> simp [qLocal, tick, hl, hk]
theorem CBs_end {α cx K} {x : M α} (h : x = K cx) : CBs (letEnd x) cx [] K := by
  intro vs; simp [letEnd, bindLocals, h]
theorem CBs_let {α cx x xs K} {k : Nat → List Val → M α}
    (h : ∀ c, CBs (k c) { cx with env := (x, c) :: cx.env } xs K) : CBs (let1 k) cx (x :: xs) K := by
  intro vs; simp only [let1, bindLocals, bind_assoc, h]
theorem CQ_localFn {cx full name ps va b rest fin k env} (h : env = cx.env)
    (hk : ∀ c, CQ I (k c) { cx with env := (name, c) :: cx.env } full rest fin) :
    CQ I (qLocalFn name ps va b env k) cx full (.locfn name ps va b :: rest) fin := by
  subst h; intro n; cases n <;> rw [execSeq] <;> simp [qLocalFn, tick, hk]

def isLabel (s : Stat) : Bool := match s with | .label _ => true | _ => false
def labelName (s : Stat) : Option String := match s with | .label x => some x | _ => none
def notL (l : String) (s : Stat) : Bool := match s with | .label x => x != l | _ => false

theorem dropWhile_label {l x : String} : ∀ {r rest : Block}, r.dropWhile (notL l) = .label x :: rest →
    x = l ∧ ∃ pre, r = pre ++ .label x :: rest ∧ pre.all isLabel
  | [], _, h => by simp at h
  | s :: r, rest, h => by
    by_cases hs : notL l s = true
    · rw [List.dropWhile_cons_of_pos hs] at h
      obtain ⟨hx, pre, rfl, hp⟩ := dropWhile_label h
      refine ⟨hx, s :: pre, rfl, ?_⟩
      cases s <;> simp_all [notL, isLabel]
    · rw [List.dropWhile_cons_of_neg hs] at h
      cases h; simp_all [notL]

theorem trail_contains (l : String) : ∀ r : Block,
    ((r.takeWhile isLabel).filterMap labelName).contains l =
      match r.dropWhile (notL l) with | .label _ :: _ => true | _ => false
  | [] => rfl
  | s :: r => by
    cases s with
    | label x =>
      have h1 : (Stat.label x :: r).takeWhile isLabel = .label x :: r.takeWhile isLabel := by
        simp [List.takeWhile_cons, isLabel]
      rw [h1, List.filterMap_cons]
      by_cases hx : x = l
      · subst hx
        rw [List.dropWhile_cons_of_neg (by simp [notL])]
        simp [labelName]
      · rw [List.dropWhile_cons_of_pos (by simp [notL, hx]), ← trail_contains l r]
        simp [labelName, Ne.symm hx]
    | _ => simp [isLabel, notL]

theorem trail_ok (b : Block) (l : String) : labelAtEnd b l = (trail b).contains l := by
  have e : trail b = ((b.reverse.takeWhile isLabel).filterMap labelName) := rfl
  rw [e, trail_contains]
  unfold labelAtEnd
  split
  · next x rest h =>
    have h' : b.reverse.dropWhile (notL l) = .label x :: rest := h
    obtain ⟨rfl, pre, hr, hp⟩ := dropWhile_label h'
    rw [h']
    have hb : b = rest.reverse ++ .label x :: pre.reverse := by
      rw [← List.reverse_reverse b, hr]; simp
    have hd : b.drop (rest.length + 1) = pre.reverse := by
      have hl : rest.length + 1 = rest.reverse.length + 1 := by simp
      rw [hb, hl, List.drop_append]; simp
    simp only [beq_self_eq_true, Bool.true_and, decide_eq_true_eq]
    right; rw [hd, List.all_reverse]; exact hp
  · next h =>
    split
    · next x rest h2 => exact absurd h2 (h x rest)
    · rfl

theorem labels_ok (b : Block) (l : String) : hasLabel b l = (labels b).contains l := by
  induction b with
  | nil => rfl
  | cons s b ih =>
    unfold hasLabel labels at *
    rw [List.any_cons, List.filterMap_cons, ih]
    cases s with
    | label x =>
      dsimp only; rw [List.contains_cons]
      by_cases h : x = l
      · subst h; simp
      · have h1 : (x == l) = false := by simp [h]
        have h2 : (l == x) = false := by simp [Ne.symm h]
        rw [h1, h2]
    | _ => rfl

theorem CQ_stat {cx full s rest fin ss q ends all} (hs : CS I ss cx s) (hq : CQ I q cx full rest fin)
    (hns : s.isDecl = false) (he : trail full = ends) (ha : labels full = all) :
    CQ I (qStat ss (gotos ends all) q) cx full (s :: rest) fin := by
  subst he ha
  intro n; cases n with
  | zero => rw [execSeq]; rfl
  | succ n =>
    have e : execSeq I.srcs I.oracle I.tgt (n + 1) cx full (s :: rest) fin = (do
        match ← execStat I.srcs I.oracle I.tgt n cx s with
        | .norm => execSeq I.srcs I.oracle I.tgt n cx full rest fin
        | .goto l =>
          if labelAtEnd full l then pure .norm
          else if hasLabel full l then throw (.eff "goto: a label that does not end its block" [])
          else pure (.goto l)
        | fl => pure fl) := by
      rw [execSeq] <;> first | rfl | (intros; subst_vars; simp [Stat.isDecl] at hns)
    rw [e]; simp only [qStat, tick, hs, hq, gotos, trail_ok, labels_ok]

-- ---------- chunks loaded at run time: load, loadstring, dofile, require ----------

theorem bind_ok {α β} {x : M α} {f : α → M β} {h h' : Heap} {a : α} (e : x h = .ok a h') :
    (x >>= f) h = f a h' := by
  show EStateM.bind x f h = _; simp only [EStateM.bind, e]

theorem getTbl_ok {h : Heap} {a : Nat} {t : Tbl} (ha : h[a]? = some (.tbl t)) : getTbl a h = .ok t h := by
  simp only [getTbl, getObj, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, ha]; rfl
theorem metaOf_ok {h : Heap} {a m : Nat} {t tm : Tbl} {ev : String} (ha : h[a]? = some (.tbl t)) (hma : t.mt = some m)
    (hm : h[m]? = some (.tbl tm)) (hw : tm.mt = none) : metaOf (.tbl a) ev h = .ok (tm.get (lstr ev)) h := by
  simp only [metaOf, bind, EStateM.bind, getTbl_ok ha, hma, wget, getTbl_ok hm, held, weakOf, hw, pure,
    EStateM.pure, Bool.false_and]; rfl

/-- tostring of a value with `__tostring`: the metamethod's call in tostring's place -/
theorem callPrim_tostring {I : Sem} {n : Nat} {v f : Val} {rest : List Val} {h : Heap}
    (hm : metaOf v "__tostring" h = .ok f h) (hf : f ≠ .nil) :
    callPrim I.srcs I.oracle I.tgt (n + 1) "tostring" [] (v :: rest) h = unframe (call I.srcs I.oracle I.tgt n f [v]) h := by
  rw [callPrim]; simp only [anyArg, List.length_cons, Nat.zero_lt_succ, ↓reduceIte, List.headD_cons]
  rw [bind_ok (rfl : (pure () : M Unit) h = .ok () h), bind_ok hm]; cases f <;> first | exact (hf rfl).elim | rfl

/-- `load(s)` or `loadstring(s)`, and a chunk name or none: the parse of `s` as a closure. The parse is the parser's
(trusted, as `f_body` is), so a proof takes it as a hypothesis: `lua-lean lift` writes a source known when it lifts
as `f_loadN_body` -/
theorem call_load (I : Sem) (n : Nat) (fname : String) (hf : fname = "load" ∨ fname = "loadstring")
    (s : List Char) (cn : Option (List Char)) (b : Block) (h : Heap)
    (hb : s.head? ≠ some '\x1b') (hp : parseChunk s (shortSrc (cn.getD s)) = .ok b) :
    call I.srcs I.oracle I.tgt (n + 2) (.prim fname []) (.str s :: cn.toList.map .str) h =
      .ok [.fn h.size] (h.push (.clo ⟨[], true, b, []⟩)) := by
  rcases hf with rfl | rfl <;> rcases cn with _ | c <;>
    simp_all [call, callPrim, optStr, argStr, loadSrc, frame, alloc, bind, EStateM.bind, pure, EStateM.pure, get, getThe,
      MonadStateOf.get, EStateM.get, set, MonadStateOf.set, EStateM.set, Functor.map, EStateM.map]

/-- `string.dump(f)`, or with a flag not a dump: f's dump, stripped as `dumpStrip` reads the flag -/
theorem call_dump (I : Sem) (n a : Nat) (rest : List Val) (hr : (rest.headD .nil).isDump = false) :
    call I.srcs I.oracle I.tgt (n + 2) (.prim "string.dump" []) (.fn a :: rest) =
      pure [.dump a (dumpStrip (rest.headD .nil))] := by
  funext h; rw [call, callPrim] <;> try decide
  rw [basicFn] <;> try decide
  cases rest <;> simp_all [dumpFn, noDump, frame, bind, EStateM.bind, pure, EStateM.pure]

/-- `load(d)` or `loadstring(d)` of a dump, with a chunk name or none: `loadDump`, the dumped closure's function -/
theorem call_load_dump (I : Sem) (n : Nat) (fname : String) (hf : fname = "load" ∨ fname = "loadstring")
    (a : Nat) (s : Bool) (cn : Option (List Char)) :
    call I.srcs I.oracle I.tgt (n + 2) (.prim fname []) (.dump a s :: cn.toList.map .str) = frame (loadDump a s (shortSrc (cn.getD "=?".toList)) none) := by
  funext h
  rcases hf with rfl | rfl <;> rcases cn with _ | c <;>
    simp [call, callPrim, optStr, argStr, frame, bind, EStateM.bind, pure, EStateM.pure, Functor.map, EStateM.map]

/-- a chunk's closure, made and called at once: `k`, the function it is (a lifted `chunk`), on the arguments -/
theorem alloc_call {β} (I : Sem) (n : Nat) (c : Clo) (args : List Val) (k : List Val → Nat → M (List Val))
    (hk : CFn I k c) (r : List Val → M β) :
    (alloc (.clo c) >>= fun f => call I.srcs I.oracle I.tgt (n + 1) (.fn f) args >>= r) =
      (alloc (.clo c) >>= fun _ => k args n >>= r) := by
  funext h
  simp only [bind, EStateM.bind, alloc, get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
    EStateM.set, pure, EStateM.pure]
  rw [call_fn I n _ args _ c (by simp), hk]

/-- `dofile(p)` of a file given as source: its chunk, `k`, on no arguments, where a yield cannot cross -/
theorem call_dofile (I : Sem) (n : Nat) (p : List Char) (b : Block) (k : List Val → Nat → M (List Val)) (h : Heap)
    (hk : CFn I k ⟨[], true, b, []⟩) (hs : I.srcs (String.ofList p) = some b) :
    call I.srcs I.oracle I.tgt (n + 3) (.prim "dofile" []) [.str p] h =
      frame (bounded 1 (do let _ ← alloc (.clo ⟨[], true, b, []⟩); k [] n)) h := by
  have e : ∀ X Y : M (List Val), X h = Y h → frame X h = frame Y h := fun X Y e => by simp only [frame, e]
  rw [call, callPrim]; apply e
  have ho : optStr "dofile" 0 [.str p] = pure (some p) := rfl
  simp only [ho, pure_bind, hs]
  have := alloc_call I n ⟨[], true, b, []⟩ [] k hk pure
  simp only [bind_pure] at this
  rw [this]

/-- `require m` of a module given as source and not yet loaded (lib_package.c): its chunk, `k`, on its name -/
def S.requireK (m : List Char) (c : Clo) (k : List Val → Nat → M (List Val)) (n : Nat) : M (List Val) := do
  rawset LOADED (.str m) SENTINEL
  let r := (← bounded 1 (do let _ ← alloc (.clo c); k [.str m] n)).headD .nil
  if !r.isNil then rawset LOADED (.str m) r
  let v ← rawget LOADED (.str m)
  if isSentinel v then rawset LOADED (.str m) (.bool true); return [.bool true]
  return [v]

/-- `require m`: not in package.loaded, not `table.new` or `table.clear`, the first file of package.path given as
source is `b`, its chunk `k` -/
theorem call_require (I : Sem) (n : Nat) (m p : List Char) (b : Block) (k : List Val → Nat → M (List Val))
    (h : Heap) (v : Val) (hk : CFn I k ⟨[], true, b, []⟩)
    (hl : rawget LOADED (.str m) h = .ok v h) (hv : v.truthy = false)
    (hn : m ≠ "table.new".toList ∧ m ≠ "table.clear".toList)
    (hp : rawget PACKAGE (lstr "path") h = .ok (.str p) h)
    (hf : (pathFiles p (modPath m)).findSome? I.srcs = some b) :
    call I.srcs I.oracle I.tgt (n + 3) (.prim "require" []) [.str m] h =
      frame (S.requireK m ⟨[], true, b, []⟩ k n) h := by
  have e : ∀ X Y : M (List Val), X h = Y h → frame X h = frame Y h := fun X Y e => by simp only [frame, e]
  rw [call, callPrim]; apply e
  simp only [List.getD_cons_zero, argStr, pure_bind]
  rw [bind_ok hl]
  have h1 : (m == "table.new".toList || m == "table.clear".toList) = false := by
    rw [Bool.or_eq_false_iff]; exact ⟨beq_false_of_ne hn.1, beq_false_of_ne hn.2⟩
  simp only [hv, Bool.false_eq_true, ↓reduceIte, h1]
  rw [bind_ok hp]
  simp only [hf, S.requireK]
  have := alloc_call I n ⟨[], true, b, []⟩ [.str m] k hk pure
  simp only [bind_pure] at this
  rw [this]

-- ---------- coroutines ----------

/-- `coroutine.resume(co, ...)`: `resumeBegin`, then the coroutine's run (the replay of its resumes so far, then
this one) and `resumeEnd`; LuaJIT's message if it cannot be resumed -/
theorem call_resume (I : Sem) (n a : Nat) (args : List Val) :
    call I.srcs I.oracle I.tgt (n + 2) (.prim "coroutine.resume" []) (.thr a :: args) =
      frame (do
        match ← resumeBegin a args with
        | .error m => pure [.bool false, lstr m]
        | .ok (prev, hist, f, a1) =>
          let r ← coRun (call I.srcs I.oracle I.tgt n f a1)
          resumeEnd a prev hist r
          pure (resumeVals r)) := by
  funext h; rw [call, callPrim]; rfl

/-- `coroutine.yield(...)` -/
theorem call_yield (I : Sem) (n : Nat) (vs : List Val) :
    call I.srcs I.oracle I.tgt (n + 2) (.prim "coroutine.yield" []) vs = frame (yieldFn vs) := by
  funext h; rw [call, callPrim] <;> first | decide | (rw [basicFn] <;> first | decide | rfl)

theorem readCell_ok {h : Heap} {c : Nat} {v : Val} (hc : h[c]? = some (.cell v)) : readCell c h = .ok v h := by
  simp only [readCell, getObj, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hc, pure, EStateM.pure]
theorem getThr_ok {h : Heap} {a : Nat} {t : Thr Heap} (ht : h[a]? = some (.thr t)) : getThr a h = .ok t h := by
  simp only [getThr, getObj, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, ht, pure, EStateM.pure]
/-- a yield with no resume left to replay, outside a builtin calling back: the run stops, suspended -/
theorem yield_susp {h : Heap} {a : Nat} {t : Thr Heap} {vs : List Val} (hc : h[CUR]? = some (.cell (.thr a)))
    (ht : h[a]? = some (.thr t)) (hb : t.bound = 0) (hs : t.script = []) : yieldFn vs h = .error (.yld vs) h := by
  have e1 := readCell_ok hc
  have e2 := getThr_ok ht
  simp only [yieldFn, bind, EStateM.bind, e1, e2, hb, hs]
  rfl

/-- a yield in a replay: the next resume's arguments, in the heap that resume went on in -/
theorem yield_replay {h h1 : Heap} {a : Nat} {t t1 : Thr Heap} {vs ws : List Val} {rest : List (List Val × Heap)}
    (hc : h[CUR]? = some (.cell (.thr a)))
    (ht : h[a]? = some (.thr t)) (hb : t.bound = 0) (hs : t.script = (ws, h1) :: rest) (ht1 : h1[a]? = some (.thr t1)) :
    yieldFn vs h = .ok ws (h1.set! a (.thr { t1 with script := rest })) := by
  have e1 := readCell_ok hc
  have e2 := getThr_ok ht
  have e3 := getThr_ok ht1
  simp only [yieldFn, bind, EStateM.bind, e1, e2, hb, hs]
  simp [set, MonadStateOf.set, EStateM.set, EStateM.bind, e3, putThr, modify, modifyGet, MonadStateOf.modifyGet,
    EStateM.modifyGet, pure, EStateM.pure]

-- functions
theorem CFn_fn {c : Clo} {k : List Val → Nat → List Val → M Flow} (hk : ∀ args n, CBs (k args n) ⟨c.env, []⟩ c.params (fun cx =>
      execBlock I.srcs I.oracle I.tgt n { cx with va := if c.va then args.drop c.params.length else [] } c.body)) :
    CFn I (fn k) c := by
  intro args n; simp only [fn, callClo, hk, bind_assoc]

end
end Lua
