import SwarmModel.Sql

/-! The text of a statement, as the Lua writes it, to `Sql.Stmt`: a lexer and a recursive-descent parser for the
subset `../lua/test/sql_inventory.lua` lists, with sqlite's operator precedence (OR, AND, NOT, `= != is in like`,
`< <= > >=`, `+ -`, `||`). `parse` reads one statement or a script; recursion runs on fuel, so `decide` evaluates it. -/

namespace Swarm.Sql

inductive Tok where
  | id (s : String) | str (s : String) | num (n : Nat) | sym (s : String) | q
  deriving DecidableEq, Repr, Inhabited

/-- a token and where it is in the text (start, end) -/
structure Tk where
  t : Tok
  b : Nat
  e : Nat
  deriving Repr, Inhabited

/-- a quoted literal's body (`''` is a quote) and the text after its closing quote -/
def strLit : List Char → Option (List Char × List Char)
  | '\'' :: '\'' :: r => (strLit r).map fun (s, rest) => ('\'' :: s, rest)
  | '\'' :: r => some ([], r)
  | c :: r => (strLit r).map fun (s, rest) => (c :: s, rest)
  | [] => none

def idChar (c : Char) : Bool := c.isAlphanum || c == '_'

def syms2 : List String := ["||", "!=", "<>", "<=", ">=", "=="]
def syms1 : List Char := ['=', '<', '>', '(', ')', ',', '.', '*', '+', '-', ';']

def lex : Nat → List Char → Nat → Except String (List Tk)
  | 0, _, _ => .error "lex: out of fuel"
  | _ + 1, [], _ => .ok []
  | n + 1, c :: r, p =>
    let l := c :: r
    if isSpace c then lex n r (p + 1)
    else if c.isAlpha || c == '_' then
      let w := l.takeWhile idChar
      return ⟨.id (String.ofList w), p, p + w.length⟩ :: (← lex n (l.drop w.length) (p + w.length))
    else if c.isDigit then
      let w := l.takeWhile Char.isDigit
      return ⟨.num (natOf w), p, p + w.length⟩ :: (← lex n (l.drop w.length) (p + w.length))
    else if c == '\'' then
      match strLit r with
      | some (s, rest) =>
        let k := l.length - rest.length
        return ⟨.str (String.ofList s), p, p + k⟩ :: (← lex n rest (p + k))
      | none => .error "lex: unclosed quote"
    else if c == '?' then return ⟨.q, p, p + 1⟩ :: (← lex n r (p + 1))
    else
      let two := String.ofList (l.take 2)
      if syms2.contains two then return ⟨.sym two, p, p + 2⟩ :: (← lex n (l.drop 2) (p + 2))
      else if syms1.contains c then return ⟨.sym c.toString, p, p + 1⟩ :: (← lex n r (p + 1))
      else .error s!"lex: {c}"

structure PS where
  src : List Char
  toks : List Tk
  /-- `?`s so far -/
  nparam : Nat := 0
  /-- an aggregate in the select being read -/
  agg : Bool := false
  /-- where the last token taken ends -/
  last : Nat := 0

abbrev P := StateT PS (Except String)

def lower (s : String) : String := String.ofList (s.toList.map lowerC)

/-- words that end an expression or a list, so never a bare alias -/
def reserved : List String :=
  ["from", "where", "group", "order", "limit", "join", "on", "as", "and", "or", "not", "is", "in", "like", "select",
   "desc", "asc", "by", "values", "set", "returning", "when", "then", "else", "end", "case", "exists", "null",
   "distinct", "do", "primary", "default", "union"]

def peek : P (Option Tok) := return (← get).toks.head?.map (·.t)
def peek2 : P (Option Tok) := return ((← get).toks.drop 1).head?.map (·.t)

def adv : P Tk := do
  let s ← get
  match s.toks with
  | t :: r => set { s with toks := r, last := t.e }; return t
  | [] => throw "unexpected end"

def isKw (k : String) : Option Tok → Bool
  | some (.id s) => lower s == k | _ => false

/-- take the keyword if it is next -/
def kw (k : String) : P Bool := do
  if isKw k (← peek) then let _ ← adv; return true else return false

def expect (k : String) : P Unit := do
  if !(← kw k) then throw s!"expected {k} at {repr ((← get).toks.head?.map (·.t))}"

def sym (k : String) : P Bool := do
  if (← peek) == some (.sym k) then let _ ← adv; return true else return false

def expectSym (k : String) : P Unit := do
  if !(← sym k) then throw s!"expected {k} at {repr ((← get).toks.head?.map (·.t))}"

def ident : P String := do
  match (← adv).t with
  | .id s => return s
  | t => throw s!"expected a name at {repr t}"

/-- a bare name that isn't a keyword, if next -/
def alias? : P (Option String) := do
  match ← peek with
  | some (.id s) => if reserved.contains (lower s) then return none else return some (← ident)
  | _ => return none

def idents : P (List String) := do
  let mut r := [← ident]
  for _ in [0:64] do
    if !(← sym ",") then break
    r := r ++ [← ident]
  return r

def param : P Expr := do
  let s ← get
  set { s with nparam := s.nparam + 1 }
  return .param s.nparam

mutual
def pExpr : Nat → P Expr
  | 0 => throw "too deep"
  | n + 1 => do let a ← pAnd n; pOr n a

def pOr : Nat → Expr → P Expr
  | 0, _ => throw "too deep"
  | n + 1, a => do if ← kw "or" then let b ← pAnd n; pOr n (.bin .or a b) else return a

def pAnd : Nat → P Expr
  | 0 => throw "too deep"
  | n + 1 => do let a ← pNot n; pAndR n a

def pAndR : Nat → Expr → P Expr
  | 0, _ => throw "too deep"
  | n + 1, a => do if ← kw "and" then let b ← pNot n; pAndR n (.bin .and a b) else return a

def pNot : Nat → P Expr
  | 0 => throw "too deep"
  | n + 1 => do if ← kw "not" then return .not (← pNot n) else let a ← pRel n; pEq n a

def pEq : Nat → Expr → P Expr
  | 0, _ => throw "too deep"
  | n + 1, a => do
    let t ← peek
    if t == some (.sym "=") || t == some (.sym "==") then let _ ← adv; pEq n (.bin .eq a (← pRel n))
    else if t == some (.sym "!=") || t == some (.sym "<>") then let _ ← adv; pEq n (.bin .ne a (← pRel n))
    else if ← kw "is" then
      let op := if ← kw "not" then BinOp.isNot else .is
      pEq n (.bin op a (← pRel n))
    else if ← kw "like" then pEq n (.bin .like a (← pRel n))
    else if ← kw "in" then pEq n (← pIn n false a)
    else if isKw "not" t && (isKw "in" (← peek2) || isKw "like" (← peek2)) then
      let _ ← adv
      if ← kw "in" then pEq n (← pIn n true a)
      else let _ ← adv; pEq n (.not (.bin .like a (← pRel n)))
    else return a

def pIn : Nat → Bool → Expr → P Expr
  | 0, _, _ => throw "too deep"
  | n + 1, ng, a => do
    expectSym "("
    if isKw "select" (← peek) then
      let s ← pSelect n
      expectSym ")"
      return .inSel ng a s
    let l ← pList n
    expectSym ")"
    return .inList ng a l

def pList : Nat → P (List Expr)
  | 0 => throw "too deep"
  | n + 1 => do
    let a ← pExpr n
    if ← sym "," then return a :: (← pList n) else return [a]

def pRel : Nat → P Expr
  | 0 => throw "too deep"
  | n + 1 => do let a ← pAdd n; pRelR n a

def pRelR : Nat → Expr → P Expr
  | 0, _ => throw "too deep"
  | n + 1, a => do
    let op := match ← peek with
      | some (.sym "<") => some BinOp.lt | some (.sym "<=") => some .le
      | some (.sym ">") => some .gt | some (.sym ">=") => some .ge | _ => none
    match op with
    | some op => let _ ← adv; pRelR n (.bin op a (← pAdd n))
    | none => return a

def pAdd : Nat → P Expr
  | 0 => throw "too deep"
  | n + 1 => do let a ← pCat n; pAddR n a

def pAddR : Nat → Expr → P Expr
  | 0, _ => throw "too deep"
  | n + 1, a => do
    if ← sym "+" then pAddR n (.bin .add a (← pCat n))
    else if ← sym "-" then pAddR n (.bin .sub a (← pCat n))
    else return a

def pCat : Nat → P Expr
  | 0 => throw "too deep"
  | n + 1 => do let a ← pUn n; pCatR n a

def pCatR : Nat → Expr → P Expr
  | 0, _ => throw "too deep"
  | n + 1, a => do if ← sym "||" then pCatR n (.bin .concat a (← pUn n)) else return a

def pUn : Nat → P Expr
  | 0 => throw "too deep"
  | n + 1 => do
    if ← sym "-" then return .neg (← pUn n)
    else if ← sym "+" then pUn n
    else pPrim n

def pCase : Nat → P (List Expr × List Expr)
  | 0 => throw "too deep"
  | n + 1 => do
    if ← kw "when" then
      let c ← pExpr n
      expect "then"
      let v ← pExpr n
      let (cs, vs) ← pCase n
      return (c :: cs, v :: vs)
    else return ([], [])

def pPrim : Nat → P Expr
  | 0 => throw "too deep"
  | n + 1 => do
    let t ← adv
    match t.t with
    | .num k => return .lit (.int k)
    | .str s => return .lit (.text s)
    | .q => param
    | .sym "(" =>
      if isKw "select" (← peek) then
        let s ← pSelect n
        expectSym ")"
        return .sub s
      let e ← pExpr n
      expectSym ")"
      return e
    | .id w =>
      let l := lower w
      if l == "null" then return .lit .null
      if l == "exists" then
        expectSym "("
        let s ← pSelect n
        expectSym ")"
        return .exists s
      if l == "case" then
        let (cs, vs) ← pCase n
        let els ← if ← kw "else" then pExpr n else pure (.lit .null)
        expect "end"
        return .case cs vs els
      if l == "cast" then
        expectSym "("
        let e ← pExpr n
        expect "as"
        let ty ← ident
        expectSym ")"
        return .cast e ty
      if (← peek) == some (.sym "(") then
        let _ ← adv
        if l == "count" && (← sym "*") then
          expectSym ")"
          modify fun s => { s with agg := true }
          return .countStar
        let args ← if (← peek) == some (.sym ")") then pure [] else pList n
        expectSym ")"
        if l == "max" && args.length == 1 then modify fun s => { s with agg := true }
        return .call l args
      if ← sym "." then return .col (some w) (← ident)
      if reserved.contains l then throw s!"unexpected {w}"
      return .col none w
    | t => throw s!"unexpected {repr t}"

/-- result columns -/
def pCols : Nat → P (List SelCol)
  | 0 => throw "too deep"
  | n + 1 => do
    let c ← if ← sym "*" then pure (SelCol.star none) else
      match ← peek, ← peek2 with
      | some (.id q), some (.sym ".") =>
        if ((← get).toks.drop 2).head?.map (·.t) == some (.sym "*") then
          let _ ← adv; let _ ← adv; let _ ← adv
          pure (.star (some q))
        else pCol n
      | _, _ => pCol n
    if ← sym "," then return c :: (← pCols n) else return [c]

def pCol : Nat → P SelCol
  | 0 => throw "too deep"
  | n + 1 => do
    let b := ((← get).toks.head?.map (·.b)).getD 0
    let e ← pExpr n
    let s ← get
    let text := String.ofList ((s.src.drop b).take (s.last - b))
    let a ← if ← kw "as" then some <$> ident else alias?
    return .expr e (a.getD (match e with | .col _ c => c | _ => text))

def pOrder : Nat → P (List OrderBy)
  | 0 => throw "too deep"
  | n + 1 => do
    let e ← pExpr n
    let d ← if ← kw "desc" then pure true else do let _ ← kw "asc"; pure false
    if ← sym "," then return .mk e d :: (← pOrder n) else return [.mk e d]

def pSelect : Nat → P Select
  | 0 => throw "too deep"
  | n + 1 => do
    expect "select"
    let outer := (← get).agg
    modify fun s => { s with agg := false }
    let distinct ← kw "distinct"
    let cols ← pCols n
    let src ← if ← kw "from" then do
        let t ← ident
        let a ← alias?
        let j ← if ← kw "join" then do
            let t2 ← ident
            let a2 ← alias?
            expect "on"
            pure (some (Join.mk t2 (a2.getD t2) (← pExpr n)))
          else pure none
        pure (some (Src.mk t (a.getD t) j))
      else pure none
    let w ← if ← kw "where" then some <$> pExpr n else pure none
    let g ← if ← kw "group" then do expect "by"; pList n else pure []
    let o ← if ← kw "order" then do expect "by"; pOrder n else pure []
    let l ← if ← kw "limit" then some <$> pExpr n else pure none
    let agg := (← get).agg
    modify fun s => { s with agg := outer }
    return .mk distinct agg cols src w g o l
end

def pAssigns (n : Nat) : P (List (String × Expr)) := do
  let mut r := []
  for _ in [0:64] do
    let c ← ident
    expectSym "="
    r := r ++ [(c, ← pExpr n)]
    if !(← sym ",") then break
  return r

/-- a literal, for a column's default: its text and value -/
def pLit : P (String × Val) := do
  let t ← adv
  match t.t with
  | .num k => return (toString k, .int k)
  | .str s => return ("'" ++ s ++ "'", .text s)
  | .id w => if lower w == "null" then return ("NULL", .null) else throw s!"default {w}"
  | .sym "-" => match (← adv).t with
    | .num k => return ("-" ++ toString k, .int (-(k : Int)))
    | t => throw s!"default -{repr t}"
  | t => throw s!"default {repr t}"

/-- a column definition: name, type words, `primary key [autoincrement]`, `default lit`; whether it is the key -/
def pColDef : P (Col × Bool × Bool) := do
  let name ← ident
  let mut tys : List String := []
  for _ in [0:8] do
    match ← peek with
    | some (.id w) => if ["primary", "default", "not", "unique"].contains (lower w) then break else tys := tys ++ [← ident]
    | _ => break
  let ty := " ".intercalate tys
  let mut pk := false
  let mut auto := false
  let mut dflt : Option (String × Val) := none
  for _ in [0:4] do
    if ← kw "primary" then expect "key"; pk := true; auto ← kw "autoincrement"
    else if ← kw "default" then dflt := some (← pLit)
    else break
  return ({ name, ty, dflt := dflt.map (·.1), dfltV := (affOf ty).apply ((dflt.map (·.2)).getD .null) }, pk, auto)

def pStmt (n : Nat) : P Stmt := do
  if isKw "select" (← peek) then
    let a ← pSelect n
    if ← kw "union" then
      expect "all"
      return .unionAll a (← pSelect n)
    return .select a
  if ← kw "insert" then
    let or_ ← if ← kw "or" then do
        if ← kw "ignore" then pure OnConflict.ignore else do expect "replace"; pure .replace
      else pure .abort
    expect "into"
    let t ← ident
    let cols ← if ← sym "(" then do let c ← idents; expectSym ")"; pure (some c) else pure none
    let (vals, sel) ← if ← kw "values" then do
        let mut rows := []
        for _ in [0:64] do
          expectSym "("
          rows := rows ++ [← pList n]
          expectSym ")"
          if !(← sym ",") then break
        pure (rows, none)
      else pure ([], some (← pSelect n))
    let up ← if ← kw "on" then do
        expect "conflict"; expectSym "("
        let target ← idents
        expectSym ")"; expect "do"; expect "update"; expect "set"
        pure (some (target, ← pAssigns n))
      else pure none
    let ret ← if ← kw "returning" then pCols n else pure []
    return .insert or_ t cols vals sel up ret
  if ← kw "update" then
    let t ← ident
    expect "set"
    let sets ← pAssigns n
    let w ← if ← kw "where" then some <$> pExpr n else pure none
    return .update t sets w
  if ← kw "delete" then
    expect "from"
    let t ← ident
    let w ← if ← kw "where" then some <$> pExpr n else pure none
    return .delete t w
  if ← kw "create" then
    if ← kw "index" then
      expect "if"; expect "not"; expect "exists"
      let _ ← ident; expect "on"; let _ ← ident; expectSym "("; let _ ← idents; expectSym ")"
      return .createIndex
    expect "table"; expect "if"; expect "not"; expect "exists"
    let t ← ident
    expectSym "("
    let mut cols := []
    let mut pk := []
    let mut rowid := false
    let mut auto := false
    for _ in [0:64] do
      if ← kw "primary" then
        expect "key"; expectSym "("
        pk := ← idents
        expectSym ")"
      else
        let (c, k, a) ← pColDef
        cols := cols ++ [c]
        if k then pk := [c.name]; rowid := lower c.ty == "integer"; auto := a
      if !(← sym ",") then break
    expectSym ")"
    return .create t cols pk rowid auto
  if ← kw "alter" then
    expect "table"
    let t ← ident
    if ← kw "add" then
      expect "column"
      let (c, _, _) ← pColDef
      return .addCol t c
    expect "drop"; expect "column"
    return .dropCol t (← ident)
  if ← kw "pragma" then
    let p ← ident
    if lower p == "table_info" then
      expectSym "("
      let t ← ident
      expectSym ")"
      return .tableInfo t
    if lower p == "journal_mode" then
      expectSym "="
      return .journal (← ident)
    throw s!"pragma {p}"
  if ← kw "begin" then let _ ← kw "immediate"; return .begin
  if ← kw "commit" then return .commit
  if ← kw "rollback" then return .rollback
  throw s!"unexpected {repr (← peek)}"

/-- statements separated by `;` -/
def pScript (n : Nat) : Nat → P (List Stmt)
  | 0 => throw "too many statements"
  | k + 1 => do
    while ← sym ";" do pure ()
    if (← get).toks.isEmpty then return []
    let s ← pStmt n
    if (← get).toks.isEmpty then return [s]
    expectSym ";"
    return s :: (← pScript n k)

/-- a statement or a script, and how many `?` it has -/
def parse (sql : String) : Except String (List Stmt × Nat) := do
  let cs := sql.toList
  let toks ← lex (cs.length + 1) cs 0
  let (r, s) ← (pScript (8 * toks.length + 64) 32).run { src := cs, toks }
  return (r, s.nparam)

/-- one statement (not a script) -/
def parse1 (sql : String) : Except String (Stmt × Nat) := do
  match ← parse sql with
  | ([s], k) => return (s, k)
  | _ => throw "not one statement"

end Swarm.Sql

namespace Swarm.Sql

/-! `task claim`'s write (tasks.lua), cut to state, owner and the dependency check in its WHERE: what `parse` reads from
"update task set state='claimed', owner=? where id=? and state='open' and not exists (select 1 from task d where
d.state!='done' and ','||task.deps||',' like '%,'||d.id||',%')". The kernel evaluates `exec` on it (`decide +kernel`,
seconds); it evaluates `parse` of that text too, in about two minutes. -/

def claimWrite : Stmt :=
  .update "task" [("state", .lit (.text "claimed")), ("owner", .param 0)]
    (some (.bin .and (.bin .and (.bin .eq (.col none "id") (.param 1)) (.bin .eq (.col none "state") (.lit (.text "open"))))
      (.not (.exists (.mk false false [.expr (.lit (.int 1)) "1"] (some (.mk "task" "d" none))
        (some (.bin .and (.bin .ne (.col (some "d") "state") (.lit (.text "done")))
          (.bin .like
            (.bin .concat (.bin .concat (.lit (.text ",")) (.col (some "task") "deps")) (.lit (.text ",")))
            (.bin .concat (.bin .concat (.lit (.text "%,")) (.col (some "d") "id")) (.lit (.text ",%"))))))
        [] [] none)))))

/-- #1 after #2 (claimed, not done), #3 after #4 (done) -/
def claimTasks : DB :=
  let cols : List Col := [{ name := "id", ty := "integer" }, { name := "state", ty := "text" },
    { name := "owner", ty := "text" }, { name := "deps", ty := "text" }]
  let rows : List (List Val) := [[.int 1, .text "open", .null, .text "2"], [.int 2, .text "claimed", .text "a", .null],
    [.int 3, .text "open", .null, .text "4"], [.int 4, .text "done", .null, .null]]
  [("task", { cols, rows, pk := ["id"], rowid := true, autoinc := true })]

example : (exec { db := claimTasks } claimWrite [.text "b", .int 1]).toOption.map (·.2.changes) = some 0 := by
  decide +kernel
example : (exec { db := claimTasks } claimWrite [.text "b", .int 3]).toOption.map (·.2.changes) = some 1 := by
  decide +kernel

end Swarm.Sql
