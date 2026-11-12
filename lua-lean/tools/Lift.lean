import LuaLean.Show
import LuaLean.Shallow

/-! `lua-lean lift <file.lua> [<Namespace> [<Import>:<Const>]] [--only <f>,...]` writes the Lua file as Lean: for each
of its functions (the chunk itself is `chunk`), its parsed body `f_body`, the shallow function `f` (`LuaLean/Shallow.lean`'s
combinators, every local the Lean variable naming its cell) and `f_ok`, the proof that `f` is the interpreter's
call of the closure, for every fuel: `D.fn_ok` (`LuaLean/Denote.lean`) at the closure. This printer is not trusted:
Lean checks by computation that the printed `f` is `D.fn`'s. -/

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
  /-- a chunk `load` makes from a source known here: what its body is the parse of -/
  note : String := ""

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
  /-- outside a tail call: the function is its calls' level 1 (`Ctx.top`) -/
  top : Bool := true

/-- `Ctx.caller` as the lifted code has it: `fn0` is the function's address -/
def Cx.caller (cx : Cx) : String := if cx.top then "(some fn0)" else "none"

mutual
partial def fvE (b : List String) : Exp → List String
  | .var x => if b.contains x then [] else [x]
  | .func ps _ body _ => fvS (ps.reverse ++ b) body none
  | .index t k => fvE b t ++ fvE b k
  | .call f as => fvE b f ++ as.flatMap (fvE b)
  | .method o _ as => fvE b o ++ as.flatMap (fvE b)
  | .bin _ x y | .and x y | .or x y => fvE b x ++ fvE b y
  | .un _ x | .paren x | .site _ x => fvE b x
  | .table fs => fs.flatMap fun
    | .pos e | .named _ e => fvE b e
    | .keyed k e => fvE b k ++ fvE b e
  | _ => []
partial def fvS (b : List String) : Block → Option Exp → List String
  | [], fin => match fin with | some c => fvE b c | none => []
  | .loc ns es :: rest, fin => es.flatMap (fvE b) ++ fvS (ns.reverse ++ b) rest fin
  | .locfn x ps _ body _ :: rest, fin => fvS (ps.reverse ++ x :: b) body none ++ fvS (x :: b) rest fin
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
  | .site _ s => fvT b s
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
  set { s with names := n :: s.names, jobs := s.jobs.push ⟨n, ps, va, body, scope, ""⟩ }
  pure n

/-- `load(s)` or `loadstring(s)` with `s` (and the chunk name, if given) a constant and the global `load` or
`loadstring`: the chunk it makes, lifted as a function of its own (`call_load` says the call makes its closure) -/
def loadJob (cx : Cx) (f : Exp) (as : List Exp) : T Unit := do
  let (g, s, cn) := match f, as with
    | .var g, [.str s] => (g, s, none)
    | .var g, [.str s, .str c] => (g, s, some c)
    | _, _ => ("", [], none)
  if !(g == "load" || g == "loadstring") || cx.scope.any (·.lua == g) then return
  let name := cn.getD s
  if let .ok b := parseChunk s (shortSrc name) then
    let st ← get
    let n := freshIn st.names (leanName cx.fname ++ "_load")
    let j : Job := ⟨n, [], true, b, [], s!"/-- `{g}`'s chunk: `parseChunk {chars s} (shortSrc {chars name}) = .ok {n}_body` -/\n"⟩
    set { st with names := n :: st.names, jobs := st.jobs.push j }

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

mutual
partial def tExp (cx : Cx) (e : Exp) (name : String := "") : T String := do
  match e with
  | .nil => pure "S.eNil"
  | .tru => pure "S.eTrue"
  | .fls => pure "S.eFalse"
  | .num n => pure s!"(S.eNum {num n})"
  | .cnum v u => pure s!"(S.eCnum {v} {u})"
  | .str s => pure s!"(S.eStr {chars s})"
  | .vararg => pure s!"(S.eVa {cx.va})"
  | .func ps va b ln =>
    let f ← job (if name == "" then cx.fname ++ "_fn" else name) ps va b cx.scope
    pure s!"(S.eFunc {lst (ps.map nm)} {va} {f}_body {ln} ({envOf cx}) fn0)"
  | .var x =>
    match cx.scope.find? (·.lua == x) with
    | some ent => pure s!"(S.eCell {ent.lean})"
    | none => pure s!"(S.eGlob I fn0 {nm x})"
  | .index t k => pure s!"(S.eIndex I {← tExp cx t} {← tExp cx k})"
  | .call .. | .method .. => pure s!"(S.eFirst {← tMulti cx e})"
  | .paren a => pure s!"(S.eParen {← tExp cx a})"
  | .site st a => pure s!"(S.eSite {site st} {← tExp cx a name})"
  | .and a b => pure s!"(S.eAnd {← tExp cx a} {← tExp cx b})"
  | .or a b => pure s!"(S.eOr {← tExp cx a} {← tExp cx b})"
  | .bin op a b => pure s!"(S.eBin I {Show.binop op} {← tExp cx a} {← tExp cx b})"
  | .un op a => pure s!"(S.eUn I {Show.unop op} {← tExp cx a})"
  | .table fs => pure s!"(S.eTable {← tFields cx fs})"

partial def tMulti (cx : Cx) (e : Exp) : T String := do
  match e with
  | .call f as => do
    loadJob cx f as
    let sf ← tExp cx f
    pure s!"(S.mCall I {cx.caller} {sf} {← tList cx as})"
  | .method o m as => do
    let so ← tExp cx o
    pure s!"(S.mMethod I {cx.caller} {so} {nm m} {← tList cx as})"
  | .vararg => pure s!"(S.mVa {cx.va})"
  | .site st a => pure s!"(S.mSite {site st} {← tMulti { cx with top := cx.top && !st.tail } a})"
  | e => pure s!"(S.mOne {← tExp cx e})"

partial def tList (cx : Cx) (es : List Exp) (names : List String := []) : T String := do
  match es with
  | [] => pure "S.lNil"
  | [e] => do
    let m ← match e with
      | .func .. => pure s!"(S.mOne {← tExp cx e (names.headD "")})"
      | _ => tMulti cx e
    pure s!"(S.lLast {m})"
  | e :: es => do
    let s ← tExp cx e (names.headD "")
    pure s!"(S.lCons {s} {← tList cx es names.tail})"

partial def tFields (cx : Cx) (fs : List Field) : T String := do
  match fs with
  | [] => pure "S.fNil"
  | [.pos e] => pure s!"(S.fLast {← tMulti cx e})"
  | .pos e :: fs => do
    let s ← tExp cx e
    pure s!"(S.fPos {s} {← tFields cx fs})"
  | .named k e :: fs => do
    let s ← tExp cx e (cx.fname ++ "_" ++ k)
    pure s!"(S.fNamed {nm k} {s} {← tFields cx fs})"
  | .keyed k e :: fs => do
    let sk ← tExp cx k
    let s ← tExp cx e
    pure s!"(S.fKeyed {sk} {s} {← tFields cx fs})"

partial def tPlaces (cx : Cx) (ts : List Exp) : T String := do
  match ts with
  | [] => pure "S.pNil"
  | .var x :: ts => do
    let w := match cx.scope.find? (·.lua == x) with
      | some ent => s!"(S.wCell {ent.lean})"
      | none => s!"(S.wGlob I fn0 {nm x})"
    pure s!"(S.pVar {w} {← tPlaces cx ts})"
  | .site s (.index t k) :: ts => do
    let st ← tExp cx t
    let sk ← tExp cx k
    pure s!"(S.pIndex I (some {site s}) {st} {sk} {← tPlaces cx ts})"
  | .index t k :: ts => do
    let st ← tExp cx t
    let sk ← tExp cx k
    pure s!"(S.pIndex I none {st} {sk} {← tPlaces cx ts})"
  | _ => pure "UNSUPPORTED"

/-- a name for the function an assignment or local makes -/
partial def targetName : Exp → String
  | .var x => x
  | .index t (.str k) => targetName t ++ "_" ++ String.ofList k
  | .site _ e => targetName e
  | _ => ""

partial def tStat (cx : Cx) (s : Stat) : T String := do
  match s with
  | .assign ts es => do
    let sp ← tPlaces cx ts
    pure s!"(S.sAssign {sp} {← tList cx es (ts.map targetName)})"
  | .call e => pure s!"(S.sCall {← tMulti cx e})"
  | .block b => pure s!"(S.sBlock {← tBlock cx b})"
  | .while c b => do
    let sc ← tExp cx c
    pure s!"(S.sWhile {sc} {← tBlock cx b})"
  | .rpt b c => pure s!"(S.sRepeat {← tSeq { cx with ind := cx.ind ++ "  " } b b (some c)})"
  | .ite c t e => do
    let sc ← tExp cx c
    let kt ← tBlock cx t
    pure s!"(S.sIf {sc} {kt} {← tBlock cx e})"
  | .fornum v a b st body => do
    let sa ← tExp cx a
    let sb ← tExp cx b
    let sst ← match st with
      | some e => pure s!"(some {← tExp cx e})"
      | none => pure "none"
    let (cx', cs) ← bindCells cx [v]
    pure s!"(S.sForNum {sa} {sb} {sst} fun {cs.headD ""} => {← tBlock cx' body})"
  | .forin vs es body => do
    let sl ← tList cx es
    let (cx', cs) ← bindCells cx vs
    pure s!"(S.sForIn I {sl} fun n => {lets cs}S.letEnd ({← tBlock cx' body} n))"
  | .ret es => pure s!"(S.sReturn {← tList cx es})"
  | .brk => pure "S.sBreak"
  | .goto l => pure s!"(S.sGoto {nm l})"
  | .label _ => pure "S.sLabel"
  | .site st s => pure s!"(S.sSite {site st} {← tStat cx s})"
  | .loc .. | .locfn .. => pure "UNSUPPORTED"

partial def tBlock (cx : Cx) (b : Block) : T String := do
  pure s!"(S.block {← tSeq { cx with ind := cx.ind ++ "  " } b b none})"

partial def tSeq (cx : Cx) (full rest : Block) (fin : Option Exp) : T String := do
  let nl := "\n" ++ cx.ind
  match rest with
  | [] => match fin with
    | none => pure "S.qEnd"
    | some c => pure s!"(S.qEndRpt {← tExp cx c})"
  | .loc ns es :: rest => do
    let sl ← tList cx es ns
    let (cx', cs) ← bindCells cx ns
    pure s!"(S.qLocal {sl} fun n => {lets cs}S.letEnd{nl}({← tSeq cx' full rest fin} n))"
  | .locfn x ps va b ln :: rest => do
    let (cx', cs) ← bindCells cx [x]
    let f ← job x ps va b cx'.scope
    pure s!"(S.qLocalFn {nm x} {lst (ps.map nm)} {va} {f}_body {ln} ({envOf cx}) fn0 fun {cs.headD ""} =>{nl}{← tSeq cx' full rest fin})"
  | s :: rest => do
    let ss ← tStat cx s
    pure s!"(S.qStat {ss} (S.gotos {lst ((trail full).map nm)} {lst ((labels full).map nm)}){nl}{← tSeq cx full rest fin})"
end

/-- the function's def, and its theorem: `D.fn_ok` at the function's closure, with `res` the free names' cells as
`D.fn` takes them and `res1_ok` the hypotheses that they are `env0`'s -/
def fnDef (j : Job) : T String := do
  modify fun s => { s with used := [] }
  let fv := (fvS j.ps.reverse j.body none).eraseDups
  let ups := fv.filter fun x => j.scope.any (·.lua == x)
  let globs := fv.filter fun x => !j.scope.any (·.lua == x)
  let mut upEnts := []
  for x in ups do
    upEnts := upEnts ++ [(⟨x, ← fresh x, true⟩ : Ent)]
  let va := if j.va then s!"(args.drop {j.ps.length})" else "[]"
  let cx0 : Cx := ⟨upEnts.reverse, va, j.name, "    ", true⟩
  let (cx, cs) ← bindCells cx0 j.ps
  let k ← tBlock cx j.body
  let cells := String.join (upEnts.map fun e => s!" {e.lean}")
  let cellsT := if upEnts.isEmpty then "" else s!" ({" ".intercalate (upEnts.map (·.lean))} : Nat)"
  let hyps := String.join (upEnts.map fun e => s!"\n    (h_{leanName e.lua} : env0.lookup {nm e.lua} = some {e.lean})") ++
    String.join (globs.map fun x => s!"\n    (h_{leanName x} : env0.lookup {nm x} = none)")
  let frees := upEnts.map (fun e => (e.lua, s!"(some {e.lean})")) ++ globs.map (·, "none")
  let res := frees.foldr (fun (x, v) r => s!"(res1 {nm x} {v} {r})") "(fun x => env0.lookup x)"
  let resP := frees.foldr (fun (x, _) r => s!"(res1_ok h_{leanName x} {r})") "(fun _ => rfl)"
  let clo := s!"⟨{lst (j.ps.map nm)}, {j.va}, {j.name}_body, env0, fenv0, src0, ln0⟩"
  pure s!"def {j.name} (I : Sem) (env0 : Env) (fn0 : Nat){cellsT} : List Val → Nat → M (List Val) :=
  S.fn fn0 fun args n => {lets cs}S.letEnd ({k} n)

theorem {j.name}_ok (I : Sem) (env0 : Env) (fn0 fenv0 : Nat) (src0 : List Char) (ln0 : Nat × Nat){cellsT}{hyps} :
    CFn I ({j.name} I env0 fn0{cells}) fn0 {clo} :=
  D.fn_ok I {res} fn0 {clo} {resP}
"

partial def drain (i : Nat) (acc : Array (Job × String)) : T (Array (Job × String)) := do
  let s ← get
  if h : i < s.jobs.size then
    let j := s.jobs[i]
    let d ← fnDef j
    drain (i + 1) (acc.push (j, d))
  else pure acc

def main (args : List String) : IO UInt32 := do
  -- `--only f,g`: just those functions and the ones nested in them (`f_…`)
  let (args, only) := match args.reverse with
    | ns :: "--only" :: rest => (rest.reverse, some (ns.splitOn ","))
    | _ => (args, none)
  let (modName, file, src) ← match args with
    | [m, f] => pure (m, f, none)
    | [m, f, s] => pure (m, f, some s)
    | _ => do IO.eprintln "usage: Lift.lean <Namespace> <file.lua> [<Import>:<Const>] [--only <f>,...]"; return 1
  let bytes ← IO.FS.readBinFile file
  match parseChunk (bytesOf bytes) ((System.FilePath.mk file).fileName.getD file) with
  | .error e => IO.eprintln e; return 1
  | .ok b =>
    let st : St := { jobs := #[⟨"chunk", [], true, b, [], ""⟩], names := ["chunk"] }
    let (out, _) := (drain 0 #[]).run st
    let out := match only with
      | some ns => out.filter fun (p : Job × String) => let j := p.1; ns.any fun f => j.name == f || j.name.startsWith (f ++ "_")
      | none => out
    if out.any (fun (_, d) => (d.splitOn "UNSUPPORTED").length > 1) then
      IO.eprintln s!"{file}: a tree the parser does not make (an assignment target other than a name or an index)"; return 1
    let (imp, srcConst) := match src with
      | some s => match s.splitOn ":" with
        | [m, c] => (s!"\nimport {m}", some c)
        | _ => ("", none)
      | none => ("", none)
    IO.println s!"import LuaLean.Denote{imp}

/-! {(System.FilePath.mk file).fileName.getD file} lifted by `lua-lean lift`: each function's parsed body, its shallow form, and the proof
that the two are the same. GENERATED: do not edit. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace {modName}
open Lua

"
    for (j, _) in out do
      IO.println s!"{j.note}def {j.name}_body : Block :={Show.block j.body}\n"
    if let some c := srcConst then
      IO.println s!"/-- the chunk is the file as `{c}` has it -/\ntheorem chunk_body_eq : chunk_body = {c} := rfl\n"
    for (_, d) in out do
      IO.println d
    IO.println s!"end {modName}\n-- checksum {modName} {checksum bytes}"
    return 0
