import LuaLean.Show
import LuaLean.Shallow

/-! `lua-lean lift <file.lua> [<Namespace> [<Import>:<Const>]]` writes the Lua file as Lean: for each
of its functions (the chunk itself is `chunk`), its parsed body `f_body`, the shallow function `f` (`LuaLean/Shallow.lean`'s
combinators, every local the Lean variable naming its cell) and `f_ok`, the proof that `f` is the interpreter's
call of the closure, for every fuel. The translator is not trusted: Lean checks each proof. -/

open Lua Lua.Show

/-- a name in scope: the Lean variable naming its cell; `up`: it is in the closure's `env0`, not the prefix the
function's own locals make -/
structure Ent where
  lua : String
  lean : String
  up : Bool

/-- a function to write: the names visible where its closure is made -/
structure Job where
  name : String
  ps : List String
  va : Bool
  body : Block
  scope : List Ent

structure St where
  jobs : Array Job := #[]
  used : List String := []
  names : List String := []

abbrev T := StateM St

structure Cx where
  scope : List Ent
  va : String
  fname : String
  ind : String

mutual
partial def fvE (b : List String) : Exp → List String
  | .var x => if b.contains x then [] else [x]
  | .func ps _ body => fvS (ps.reverse ++ b) body none
  | .index t k => fvE b t ++ fvE b k
  | .call f as => fvE b f ++ as.flatMap (fvE b)
  | .method o _ as => fvE b o ++ as.flatMap (fvE b)
  | .bin _ x y | .and x y | .or x y => fvE b x ++ fvE b y
  | .un _ x | .paren x => fvE b x
  | .table fs => fs.flatMap fun
    | .pos e | .named _ e => fvE b e
    | .keyed k e => fvE b k ++ fvE b e
  | _ => []
partial def fvS (b : List String) : Block → Option Exp → List String
  | [], fin => match fin with | some c => fvE b c | none => []
  | .loc ns es :: rest, fin => es.flatMap (fvE b) ++ fvS (ns.reverse ++ b) rest fin
  | .locfn x ps _ body :: rest, fin => fvS (ps.reverse ++ x :: b) body none ++ fvS (x :: b) rest fin
  | s :: rest, fin => fvT b s ++ fvS b rest fin
partial def fvT (b : List String) : Stat → List String
  | .assign ts es => ts.flatMap (fvE b) ++ es.flatMap (fvE b)
  | .call e => fvE b e
  | .block body => fvS b body none
  | .while c body => fvE b c ++ fvS b body none
  | .rpt body c => fvS b body (some c)
  | .ite c t e => fvE b c ++ fvS b t none ++ fvS b e none
  | .fornum v x y st body => fvE b x ++ fvE b y ++ ((st.map (fvE b)).getD []) ++ fvS (v :: b) body none
  | .forin vs es body => es.flatMap (fvE b) ++ fvS (vs.reverse ++ b) body none
  | .ret es => es.flatMap (fvE b)
  | _ => []
end

def leanName (x : String) : String := x.map fun c => if c.isAlphanum || c == '_' then c else '_'

def freshIn (used : List String) (base : String) : String :=
  let rec go (k : Nat) (fuel : Nat) : String :=
    let n := if k == 0 then base else base ++ toString k
    match fuel with
    | 0 => n
    | f + 1 => if used.contains n then go (k + 1) f else n
  go 0 (used.length + 1)

def fresh (x : String) : T String := do
  let s ← get
  let n := freshIn s.used ("c_" ++ leanName x)
  set { s with used := n :: s.used }
  pure n

/-- Lean's keywords a Lua name can be -/
def leanKeywords : List String :=
  ["at", "by", "do", "end", "exists", "fun", "have", "show", "from", "in", "let", "match", "meta", "mut", "open",
   "then", "else", "if", "with", "where", "for", "unless", "return", "try", "catch", "finally", "break", "continue",
   "calc", "deriving", "instance", "structure", "class", "inductive", "namespace", "section", "variable", "universe",
   "example", "abbrev", "opaque", "def", "theorem", "import", "local", "private", "protected", "partial",
   "unsafe", "noncomputable", "macro", "syntax", "nomatch", "nofun", "omit", "include", "notation", "set_option"]

def job (name : String) (ps : List String) (va : Bool) (body : Block) (scope : List Ent) : T String := do
  let s ← get
  let base := leanName name
  let n := freshIn s.names (if leanKeywords.contains base then base ++ "_" else base)
  set { s with names := n :: s.names, jobs := s.jobs.push ⟨n, ps, va, body, scope⟩ }
  pure n

/-- the runtime env: the function's own locals, innermost first, then `env0` -/
def envOf (cx : Cx) : String :=
  String.join ((cx.scope.filter (!·.up)).map fun e => s!"({nm e.lua}, {e.lean}) :: ") ++ "env0"

def bindCells (cx : Cx) (names : List String) : T (Cx × List String) := do
  let mut cx := cx
  let mut cs := []
  for x in names do
    let c ← fresh x
    cx := { cx with scope := ⟨x, c, false⟩ :: cx.scope }
    cs := cs ++ [c]
  pure (cx, cs)

def lets (cs : List String) : String := String.join (cs.map fun c => s!"S.let1 fun {c} => ")
def letsP (cs : List String) : String := String.join (cs.map fun c => s!"CBs_let fun {c} => ")

/-- a name's lookup proof: in the prefix by computation, else the hypothesis about `env0` -/
def lookupPf (e : Ent) : String := if e.up then s!"h_{leanName e.lua}" else "rfl"

def hint (x : String) : Exp → Option String
  | .func .. => some x
  | _ => none

mutual
partial def tExp (cx : Cx) (e : Exp) (name : String := "") : T (String × String) := do
  match e with
  | .nil => pure ("S.eNil", "CE_nil")
  | .tru => pure ("S.eTrue", "CE_true")
  | .fls => pure ("S.eFalse", "CE_false")
  | .num n => pure (s!"(S.eNum {num n})", "CE_num")
  | .str s => pure (s!"(S.eStr {chars s})", "CE_str")
  | .vararg => pure (s!"(S.eVa {cx.va})", "(CE_va (by rfl))")
  | .func ps va b =>
    let f ← job (if name == "" then cx.fname ++ "_fn" else name) ps va b cx.scope
    pure (s!"(S.eFunc {lst (ps.map nm)} {va} {f}_body ({envOf cx}))", "(CE_func (by rfl))")
  | .var x =>
    match cx.scope.find? (·.lua == x) with
    | some ent => pure (s!"(S.eCell {ent.lean})", s!"(CE_cell {lookupPf ent})")
    | none => pure (s!"(S.eGlob {nm x})", s!"(CE_glob h_{leanName x})")
  | .index t k => do
    let (st, pt) ← tExp cx t
    let (sk, pk) ← tExp cx k
    pure (s!"(S.eIndex I {st} {sk})", s!"(CE_index {pt} {pk})")
  | .call .. => do
    let (m, pm) ← tMulti cx e
    pure (s!"(S.eFirst {m})", s!"(CE_call {pm})")
  | .method .. => do
    let (m, pm) ← tMulti cx e
    pure (s!"(S.eFirst {m})", s!"(CE_method {pm})")
  | .paren a => do
    let (s, p) ← tExp cx a
    pure (s!"(S.eParen {s})", s!"(CE_paren {p})")
  | .and a b => tBin2 cx "S.eAnd" "CE_and" a b
  | .or a b => tBin2 cx "S.eOr" "CE_or" a b
  | .bin op a b => tBin2 cx s!"S.eBin I {Show.binop op}" "CE_bin" a b
  | .un op a => do
    let (s, p) ← tExp cx a
    pure (s!"(S.eUn {Show.unop op} {s})", s!"(CE_un {p})")
  | .table fs => do
    let (s, p) ← tFields cx fs
    pure (s!"(S.eTable {s})", s!"(CE_table {p})")

partial def tBin2 (cx : Cx) (sh pf : String) (a b : Exp) : T (String × String) := do
  let (sa, pa) ← tExp cx a
  let (sb, pb) ← tExp cx b
  pure (s!"({sh} {sa} {sb})", s!"({pf} {pa} {pb})")

partial def tMulti (cx : Cx) (e : Exp) : T (String × String) := do
  match e with
  | .call f as => do
    let (sf, pf) ← tExp cx f
    let (sl, pl) ← tList cx as
    pure (s!"(S.mCall I {sf} {sl})", s!"(CM_call {pf} {pl})")
  | .method o m as => do
    let (so, po) ← tExp cx o
    let (sl, pl) ← tList cx as
    pure (s!"(S.mMethod I {so} {nm m} {sl})", s!"(CM_method {po} {pl})")
  | .vararg => pure (s!"(S.mVa {cx.va})", "(CM_va (by rfl))")
  | e => do
    let (s, p) ← tExp cx e
    pure (s!"(S.mOne {s})", s!"(CM_one rfl {p})")

partial def tList (cx : Cx) (es : List Exp) (names : List String := []) : T (String × String) := do
  match es with
  | [] => pure ("S.lNil", "CL_nil")
  | [e] => do
    let (m, pm) ← match e with
      | .func .. => do let (s, p) ← tExp cx e (names.headD ""); pure (s!"(S.mOne {s})", s!"(CM_one rfl {p})")
      | _ => tMulti cx e
    pure (s!"(S.lLast {m})", s!"(CL_last {pm})")
  | e :: es => do
    let (s, p) ← tExp cx e (names.headD "")
    let (sl, pl) ← tList cx es names.tail
    pure (s!"(S.lCons {s} {sl})", s!"(CL_cons {p} {pl})")

partial def tFields (cx : Cx) (fs : List Field) : T (String × String) := do
  match fs with
  | [] => pure ("S.fNil", "CF_nil")
  | [.pos e] => do
    let (m, pm) ← tMulti cx e
    pure (s!"(S.fLast {m})", s!"(CF_last {pm})")
  | .pos e :: fs => do
    let (s, p) ← tExp cx e
    let (sr, pr) ← tFields cx fs
    pure (s!"(S.fPos {s} {sr})", s!"(CF_pos {p} {pr})")
  | .named k e :: fs => do
    let (s, p) ← tExp cx e (cx.fname ++ "_" ++ k)
    let (sr, pr) ← tFields cx fs
    pure (s!"(S.fNamed {nm k} {s} {sr})", s!"(CF_named {p} {pr})")
  | .keyed k e :: fs => do
    let (sk, pk) ← tExp cx k
    let (s, p) ← tExp cx e
    let (sr, pr) ← tFields cx fs
    pure (s!"(S.fKeyed {sk} {s} {sr})", s!"(CF_keyed {pk} {p} {pr})")

partial def tPlaces (cx : Cx) (ts : List Exp) : T (String × String) := do
  match ts with
  | [] => pure ("S.pNil", "CP_nil")
  | .var x :: ts => do
    let (w, pw) := match cx.scope.find? (·.lua == x) with
      | some ent => (s!"(S.wCell {ent.lean})", s!"(wCell_ok {lookupPf ent})")
      | none => (s!"(S.wGlob {nm x})", s!"(wGlob_ok h_{leanName x})")
    let (sp, pp) ← tPlaces cx ts
    pure (s!"(S.pVar {w} {sp})", s!"(CP_var {pw} {pp})")
  | .index t k :: ts => do
    let (st, pt) ← tExp cx t
    let (sk, pk) ← tExp cx k
    let (sp, pp) ← tPlaces cx ts
    pure (s!"(S.pIndex I {st} {sk} {sp})", s!"(CP_index {pt} {pk} {pp})")
  | _ => pure ("UNSUPPORTED", "UNSUPPORTED")

/-- a name for the function an assignment or local makes -/
partial def targetName : Exp → String
  | .var x => x
  | .index t (.str k) => targetName t ++ "_" ++ String.ofList k
  | _ => ""

partial def tStat (cx : Cx) (s : Stat) : T (String × String) := do
  match s with
  | .assign ts es => do
    let (sp, pp) ← tPlaces cx ts
    let (sl, pl) ← tList cx es (ts.map targetName)
    pure (s!"(S.sAssign {sp} {sl})", s!"(CS_assign {pp} {pl})")
  | .call e => do
    let (m, pm) ← tMulti cx e
    pure (s!"(S.sCall {m})", s!"(CS_call {pm})")
  | .block b => do
    let (k, pk) ← tBlock cx b
    pure (s!"(S.sBlock {k})", s!"(CS_block {pk})")
  | .while c b => do
    let (sc, pc) ← tExp cx c
    let (k, pk) ← tBlock cx b
    pure (s!"(S.sWhile {sc} {k})", s!"(CS_while {pc} {pk})")
  | .rpt b c => do
    let (q, pq) ← tSeq { cx with ind := cx.ind ++ "  " } b b (some c)
    pure (s!"(S.sRepeat {q})", s!"(CS_repeat {pq})")
  | .ite c t e => do
    let (sc, pc) ← tExp cx c
    let (kt, pt) ← tBlock cx t
    let (ke, pe) ← tBlock cx e
    pure (s!"(S.sIf {sc} {kt} {ke})", s!"(CS_if {pc} {pt} {pe})")
  | .fornum v a b st body => do
    let (sa, pa) ← tExp cx a
    let (sb, pb) ← tExp cx b
    let (sst, pst) ← match st with
      | some e => do let (s, p) ← tExp cx e; pure (s!"(some {s})", p)
      | none => pure ("none", "trivial")
    let (cx', cs) ← bindCells cx [v]
    let (k, pk) ← tBlock cx' body
    pure (s!"(S.sForNum {sa} {sb} {sst} fun {cs.headD ""} => {k})", s!"(CS_fornum {pa} {pb} {pst} fun {cs.headD ""} => {pk})")
  | .forin vs es body => do
    let (sl, pl) ← tList cx es
    let (cx', cs) ← bindCells cx vs
    let (k, pk) ← tBlock cx' body
    pure (s!"(S.sForIn I {sl} fun n => {lets cs}S.letEnd ({k} n))",
      s!"(CS_forin {pl} fun n => {letsP cs}CBs_end ({pk} n))")
  | .ret es => do
    let (sl, pl) ← tList cx es
    pure (s!"(S.sReturn {sl})", s!"(CS_return {pl})")
  | .brk => pure ("S.sBreak", "CS_break")
  | .goto l => pure (s!"(S.sGoto {nm l})", "CS_goto")
  | .label _ => pure ("S.sLabel", "CS_label")
  | .loc .. | .locfn .. => pure ("UNSUPPORTED", "UNSUPPORTED")

partial def tBlock (cx : Cx) (b : Block) : T (String × String) := do
  let (q, pq) ← tSeq { cx with ind := cx.ind ++ "  " } b b none
  pure (s!"(S.block {q})", s!"(CK_block {pq})")

partial def tSeq (cx : Cx) (full rest : Block) (fin : Option Exp) : T (String × String) := do
  let nl := "\n" ++ cx.ind
  match rest with
  | [] => match fin with
    | none => pure ("S.qEnd", "CQ_end")
    | some c => do
      let (sc, pc) ← tExp cx c
      pure (s!"(S.qEndRpt {sc})", s!"(CQ_endRpt {pc})")
  | .loc ns es :: rest => do
    let (sl, pl) ← tList cx es ns
    let (cx', cs) ← bindCells cx ns
    let (sr, pr) ← tSeq cx' full rest fin
    pure (s!"(S.qLocal {sl} fun n => {lets cs}S.letEnd{nl}({sr} n))",
      s!"(CQ_local {pl} fun n => {letsP cs}CBs_end{nl}({pr} n))")
  | .locfn x ps va b :: rest => do
    let (cx', cs) ← bindCells cx [x]
    let c := cs.headD ""
    let f ← job x ps va b cx'.scope
    let (sr, pr) ← tSeq cx' full rest fin
    pure (s!"(S.qLocalFn {nm x} {lst (ps.map nm)} {va} {f}_body ({envOf cx}) fun {c} =>{nl}{sr})",
      s!"(CQ_localFn (by rfl) fun {c} =>{nl}{pr})")
  | s :: rest => do
    let (ss, ps) ← tStat cx s
    let (sr, pr) ← tSeq cx full rest fin
    pure (s!"(S.qStat {ss} (S.gotos {lst ((trail full).map nm)} {lst ((labels full).map nm)}){nl}{sr})",
      s!"(CQ_stat {ps}{nl}{pr} rfl rfl rfl)")
end

/-- the function's def and theorem -/
def fnDef (j : Job) : T String := do
  modify fun s => { s with used := [] }
  let fv := (fvS j.ps.reverse j.body none).eraseDups
  let ups := fv.filter fun x => j.scope.any (·.lua == x)
  let globs := fv.filter fun x => !j.scope.any (·.lua == x)
  let mut upEnts := []
  for x in ups do
    upEnts := upEnts ++ [(⟨x, ← fresh x, true⟩ : Ent)]
  let va := if j.va then s!"(args.drop {j.ps.length})" else "[]"
  let cx0 : Cx := ⟨upEnts.reverse, va, j.name, "    "⟩
  let (cx, cs) ← bindCells cx0 j.ps
  let (k, pk) ← tBlock cx j.body
  let cells := String.join (upEnts.map fun e => s!" {e.lean}")
  let cellsT := if upEnts.isEmpty then "" else s!" ({" ".intercalate (upEnts.map (·.lean))} : Nat)"
  let hyps := String.join (upEnts.map fun e => s!"\n    (h_{leanName e.lua} : env0.lookup {nm e.lua} = some {e.lean})") ++
    String.join (globs.map fun x => s!"\n    (h_{leanName x} : env0.lookup {nm x} = none)")
  pure s!"def {j.name} (I : Sem) (env0 : Env){cellsT} : List Val → Nat → M (List Val) :=
  S.fn fun args n => {lets cs}S.letEnd ({k} n)

theorem {j.name}_ok (I : Sem) (env0 : Env){cellsT}{hyps} :
    CFn I ({j.name} I env0{cells}) ⟨{lst (j.ps.map nm)}, {j.va}, {j.name}_body, env0⟩ :=
  CFn_fn fun args n => {letsP cs}CBs_end ({pk} n)
"

partial def drain (i : Nat) (acc : Array (Job × String)) : T (Array (Job × String)) := do
  let s ← get
  if h : i < s.jobs.size then
    let j := s.jobs[i]
    let d ← fnDef j
    drain (i + 1) (acc.push (j, d))
  else pure acc

def main (args : List String) : IO UInt32 := do
  let (modName, file, src) ← match args with
    | [m, f] => pure (m, f, none)
    | [m, f, s] => pure (m, f, some s)
    | _ => do IO.eprintln "usage: Lift.lean <Namespace> <file.lua> [<Import>:<Const>]"; return 1
  let bytes ← IO.FS.readBinFile file
  match parseChunk (bytesOf bytes) with
  | .error e => IO.eprintln e; return 1
  | .ok b =>
    let st : St := { jobs := #[⟨"chunk", [], true, b, []⟩], names := ["chunk"] }
    let (out, _) := (drain 0 #[]).run st
    if out.any (fun (_, d) => (d.splitOn "UNSUPPORTED").length > 1) then
      IO.eprintln s!"{file}: an assignment target the translator does not handle"; return 1
    let (imp, srcConst) := match src with
      | some s => match s.splitOn ":" with
        | [m, c] => (s!"\nimport {m}", some c)
        | _ => ("", none)
      | none => ("", none)
    IO.println s!"import LuaLean.Shallow{imp}

/-! {(System.FilePath.mk file).fileName.getD file} lifted by `lua-lean lift`: each function's parsed body, its shallow form, and the proof
that the two are the same. GENERATED: do not edit. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace {modName}
open Lua

"
    for (j, _) in out do
      IO.println s!"def {j.name}_body : Block :={Show.block j.body}\n"
    if let some c := srcConst then
      IO.println s!"/-- the chunk is the file as `{c}` has it -/\ntheorem chunk_body_eq : chunk_body = {c} := rfl\n"
    for (_, d) in out do
      IO.println d
    IO.println s!"end {modName}\n-- checksum {modName} {checksum bytes}"
    return 0
