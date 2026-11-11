import SwarmModel.Lua.Syntax

/-! A parser for the subset: Lua 5.1's grammar and precedence, LuaJIT's lexer (`\x`, `\z`, `goto`). It is not part
of what is proved: proofs are about the syntax tree it gives, written out as Lean (`LuaSrc.lean`). -/

namespace Swarm.Lua

inductive Token where
  | name (s : String) | kw (s : String) | num (n : Num) | str (s : List Char) | sym (s : String) | eof
  deriving Inhabited

def keywords : List String :=
  ["and", "break", "do", "else", "elseif", "end", "false", "for", "function", "goto", "if", "in", "local", "nil",
   "not", "or", "repeat", "return", "then", "true", "until", "while"]

def isAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
def isAlnum (c : Char) : Bool := isAlpha c || Num.isDigit c

/-- the level of a long bracket `[==[` at the start: some number of `=` -/
def longOpen : List Char → Option (Nat × List Char)
  | '[' :: s =>
    let n := (s.takeWhile (· == '=')).length
    match s.drop n with
    | '[' :: r => some (n, r)
    | _ => none
  | _ => none

/-- a long bracket's text up to its close, and the rest -/
partial def longBody (n : Nat) (s : List Char) (acc : List Char) : Except String (List Char × List Char) :=
  match s with
  | [] => .error "unfinished long string"
  | ']' :: r =>
    let k := (r.takeWhile (· == '=')).length
    if k == n && (r.drop k).head? == some ']' then .ok (acc.reverse, r.drop (k + 1))
    else longBody n r (']' :: acc)
  | c :: r => longBody n r (c :: acc)

def skipFirstNewline : List Char → List Char
  | '\r' :: '\n' :: r | '\n' :: '\r' :: r | '\n' :: r | '\r' :: r => r
  | r => r

partial def quoted (q : Char) (s : List Char) (acc : List Char) : Except String (List Char × List Char) :=
  match s with
  | [] => .error "unfinished string"
  | '\n' :: _ => .error "unfinished string"
  | c :: r =>
    if c == q then .ok (acc.reverse, r) else
    if c != '\\' then quoted q r (c :: acc) else
    match r with
    | 'n' :: r => quoted q r ('\n' :: acc)
    | 't' :: r => quoted q r ('\t' :: acc)
    | 'r' :: r => quoted q r ('\r' :: acc)
    | 'a' :: r => quoted q r ('\x07' :: acc)
    | 'b' :: r => quoted q r ('\x08' :: acc)
    | 'f' :: r => quoted q r ('\x0c' :: acc)
    | 'v' :: r => quoted q r ('\x0b' :: acc)
    | '\n' :: r => quoted q r ('\n' :: acc)
    | 'x' :: a :: b :: r =>
      match Num.hexVal a, Num.hexVal b with
      | some x, some y => quoted q r (Char.ofNat (16 * x + y) :: acc)
      | _, _ => .error "bad \\x escape"
    | 'z' :: r => quoted q (r.dropWhile Num.isSpace) acc
    | d :: r =>
      if Num.isDigit d then
        let ds := (d :: r).takeWhile Num.isDigit |>.take 3
        let v := ds.foldl (fun a c => 10 * a + (c.toNat - '0'.toNat)) 0
        if v > 255 then .error "escape too large" else quoted q ((d :: r).drop ds.length) (Char.ofNat v :: acc)
      else quoted q r (d :: acc)
    | [] => .error "unfinished string"

def syms3 : List String := ["..."]
def syms2 : List String := ["==", "~=", "<=", ">=", "..", "::"]
def syms1 : List Char := "+-*/%^#<>=(){}[];:,.".toList

partial def lex (s : List Char) (acc : Array Token) : Except String (Array Token) :=
  match s with
  | [] => .ok (acc.push .eof)
  | c :: r =>
    if Num.isSpace c then lex r acc
    else if c == '-' && r.head? == some '-' then
      let r := r.tail
      match longOpen r with
      | some (n, b) => do let (_, rest) ← longBody n b []; lex rest acc
      | none => lex (r.dropWhile (· != '\n')) acc
    else if isAlpha c then
      let w := (c :: r).takeWhile isAlnum
      let s := String.ofList w
      lex ((c :: r).drop w.length) (acc.push (if keywords.contains s then .kw s else .name s))
    else if Num.isDigit c || (c == '.' && (r.head?.map Num.isDigit).getD false) then
      -- a numeral: digits, letters, dots, and a sign after an exponent letter
      let rec numeral : List Char → List Char → List Char × List Char
        | x :: y :: rest, acc =>
          if (x == 'e' || x == 'E' || x == 'p' || x == 'P') && (y == '+' || y == '-') then numeral rest (y :: x :: acc)
          else if isAlnum x || x == '.' then numeral (y :: rest) (x :: acc) else (acc.reverse, x :: y :: rest)
        | [x], acc => if isAlnum x || x == '.' then ((x :: acc).reverse, []) else (acc.reverse, [x])
        | [], acc => (acc.reverse, [])
      let (w, rest) := numeral (c :: r) []
      match Num.scanNum w with
      | some (f, []) => lex rest (acc.push (.num (Num.narrow f)))
      | _ => .error s!"malformed number {String.ofList w}"
    else if c == '"' || c == '\'' then do
      let (str, rest) ← quoted c r []
      lex rest (acc.push (.str str))
    else if c == '[' && (longOpen s).isSome then do
      let (n, b) := (longOpen s).get!
      let (str, rest) ← longBody n (skipFirstNewline b) []
      lex rest (acc.push (.str str))
    else
      let w3 := String.ofList (s.take 3)
      let w2 := String.ofList (s.take 2)
      if syms3.contains w3 then lex (s.drop 3) (acc.push (.sym w3))
      else if syms2.contains w2 then lex (s.drop 2) (acc.push (.sym w2))
      else if syms1.contains c then lex r (acc.push (.sym c.toString))
      else .error s!"unexpected character {c}"

namespace Parser

structure PState where
  toks : Array Token
  pos : Nat

abbrev P := StateT PState (Except String)

def peek : P Token := do let s ← get; return s.toks.getD s.pos .eof
def peek2 : P Token := do let s ← get; return s.toks.getD (s.pos + 1) .eof
def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

def isSym (t : Token) (x : String) : Bool := match t with | .sym y => x == y | _ => false
def isKw (t : Token) (x : String) : Bool := match t with | .kw y => x == y | _ => false

def where_ : P String := do
  let s ← get
  return s!"token {s.pos}"

def expectSym (x : String) : P Unit := do
  if isSym (← peek) x then advance else throw s!"'{x}' expected at {← where_}"
def expectKw (x : String) : P Unit := do
  if isKw (← peek) x then advance else throw s!"'{x}' expected at {← where_}"
def name : P String := do
  match ← peek with
  | .name n => advance; return n
  | _ => throw s!"name expected at {← where_}"
def acceptSym (x : String) : P Bool := do
  if isSym (← peek) x then advance; return true else return false
def acceptKw (x : String) : P Bool := do
  if isKw (← peek) x then advance; return true else return false

/-- binary operators: (left priority, right priority) as Lua 5.1's lparser.c -/
def binop (t : Token) : Option (BinOp ⊕ Bool) × Nat × Nat :=
  match t with
  | .sym "+" => (some (.inl .add), 6, 6) | .sym "-" => (some (.inl .sub), 6, 6)
  | .sym "*" => (some (.inl .mul), 7, 7) | .sym "/" => (some (.inl .div), 7, 7) | .sym "%" => (some (.inl .mod), 7, 7)
  | .sym "^" => (some (.inl .pow), 10, 9) | .sym ".." => (some (.inl .concat), 5, 4)
  | .sym "==" => (some (.inl .eq), 3, 3) | .sym "~=" => (some (.inl .ne), 3, 3)
  | .sym "<" => (some (.inl .lt), 3, 3) | .sym "<=" => (some (.inl .le), 3, 3)
  | .sym ">" => (some (.inl .gt), 3, 3) | .sym ">=" => (some (.inl .ge), 3, 3)
  | .kw "and" => (some (.inr true), 2, 2) | .kw "or" => (some (.inr false), 1, 1)
  | _ => (none, 0, 0)

/-- LuaJIT folds arithmetic on two numeric constants in the parser (lj_parse.c's foldarith) -/
def fold (o : BinOp) (a b : Exp) : Exp :=
  let k := match o with
    | .add => some 0 | .sub => some 1 | .mul => some 2 | .div => some 3 | .mod => some 4 | .pow => some 5
    | _ => none
  match k, a, b with
  | some k, .num x, .num y => match Num.foldArith k x y with
    | some n => .num n
    | none => .bin o a b
  | _, _, _ => .bin o a b

def blockEnd (t : Token) : Bool :=
  match t with
  | .eof => true
  | .kw k => k == "end" || k == "else" || k == "elseif" || k == "until"
  | _ => false

mutual
partial def expr (limit : Nat := 0) : P Exp := do
  let t ← peek
  let mut e ←
    if isKw t "not" then do advance; pure (Exp.un .not (← expr 8))
    else if isSym t "-" then do
      advance
      match ← expr 8 with
      | .num k => pure (match Num.foldNeg k with | some k => Exp.num k | none => Exp.un .neg (.num k))
      | e => pure (Exp.un .neg e)
    else if isSym t "#" then do advance; pure (Exp.un .len (← expr 8))
    else simpleExp
  repeat
    let (op, l, r) := binop (← peek)
    match op with
    | some o =>
      if l > limit then
        advance
        let b ← expr r
        e := match o with
          | .inl o => fold o e b
          | .inr true => .and e b
          | .inr false => .or e b
      else break
    | none => break
  return e

partial def simpleExp : P Exp := do
  match ← peek with
  | .num n => advance; return .num n
  | .str s => advance; return .str s
  | .kw "nil" => advance; return .nil
  | .kw "true" => advance; return .tru
  | .kw "false" => advance; return .fls
  | .sym "..." => advance; return .vararg
  | .sym "{" => tableCons
  | .kw "function" => advance; let (ps, va, b) ← funcBody; return .func ps va b
  | _ => suffixedExp

partial def primaryExp : P Exp := do
  match ← peek with
  | .name n => advance; return .var n
  | .sym "(" => advance; let e ← expr; expectSym ")"; return (match e with | .num k => .num k | e => .paren e)
  | _ => throw s!"unexpected symbol at {← where_}"

partial def suffixedExp : P Exp := do
  let mut e ← primaryExp
  repeat
    let t ← peek
    if isSym t "." then advance; e := .index e (.str (← name).toList)
    else if isSym t "[" then advance; let k ← expr; expectSym "]"; e := .index e k
    else if isSym t ":" then advance; let n ← name; e := .method e n (← callArgs)
    else if isSym t "(" || isSym t "{" || (match t with | .str _ => true | _ => false) then e := .call e (← callArgs)
    else break
  return e

partial def callArgs : P (List Exp) := do
  match ← peek with
  | .str s => advance; return [.str s]
  | .sym "{" => return [← tableCons]
  | _ =>
    expectSym "("
    if ← acceptSym ")" then return []
    let es ← exprList
    expectSym ")"
    return es

partial def exprList : P (List Exp) := do
  let mut es := #[← expr]
  while ← acceptSym "," do es := es.push (← expr)
  return es.toList

partial def tableCons : P Exp := do
  expectSym "{"
  let mut fs : Array Field := #[]
  while !(isSym (← peek) "}") do
    let t ← peek
    if isSym t "[" then
      advance; let k ← expr; expectSym "]"; expectSym "="; fs := fs.push (.keyed k (← expr))
    else if (match t with | .name _ => true | _ => false) && isSym (← peek2) "=" then
      let n ← name; advance; fs := fs.push (.named n (← expr))
    else fs := fs.push (.pos (← expr))
    if !(← acceptSym ",") && !(← acceptSym ";") then break
  expectSym "}"
  return .table fs.toList

partial def funcBody : P (List String × Bool × Block) := do
  expectSym "("
  let mut ps : Array String := #[]
  let mut va := false
  if !(isSym (← peek) ")") then
    repeat
      if ← acceptSym "..." then va := true; break
      ps := ps.push (← name)
      if !(← acceptSym ",") then break
  expectSym ")"
  let b ← block
  expectKw "end"
  return (ps.toList, va, b)

partial def block : P Block := do
  let mut ss : Array Stat := #[]
  repeat
    let t ← peek
    if blockEnd t then break
    if isKw t "return" then
      advance
      let es ← if blockEnd (← peek) || isSym (← peek) ";" then pure [] else exprList
      let _ ← acceptSym ";"
      ss := ss.push (.ret es)
      break
    if ← acceptSym ";" then continue
    ss := ss.push (← stat)
  return ss.toList

partial def stat : P Stat := do
  let t ← peek
  match t with
  | .kw "if" =>
    advance
    let c ← expr; expectKw "then"
    let b ← block
    let rec rest : P Block := do
      if ← acceptKw "elseif" then
        let c ← expr; expectKw "then"; let b ← block
        return [.ite c b (← rest)]
      else if ← acceptKw "else" then
        let b ← block; expectKw "end"; return b
      else expectKw "end"; return []
    return .ite c b (← rest)
  | .kw "while" => advance; let c ← expr; expectKw "do"; let b ← block; expectKw "end"; return .while c b
  | .kw "do" => advance; let b ← block; expectKw "end"; return .block b
  | .kw "repeat" => advance; let b ← block; expectKw "until"; return .rpt b (← expr)
  | .kw "break" => advance; return .brk
  | .kw "goto" => advance; return .goto (← name)
  | .sym "::" => advance; let n ← name; expectSym "::"; return .label n
  | .kw "for" =>
    advance
    let n ← name
    if ← acceptSym "=" then
      let a ← expr; expectSym ","; let b ← expr
      let st ← if ← acceptSym "," then some <$> expr else pure none
      expectKw "do"; let body ← block; expectKw "end"
      return .fornum n a b st body
    else
      let mut ns := #[n]
      while ← acceptSym "," do ns := ns.push (← name)
      expectKw "in"
      let es ← exprList
      expectKw "do"; let body ← block; expectKw "end"
      return .forin ns.toList es body
  | .kw "function" =>
    advance
    let n ← name
    let mut target : Exp := .var n
    let mut isMethod := false
    repeat
      if ← acceptSym "." then target := .index target (.str (← name).toList)
      else if ← acceptSym ":" then target := .index target (.str (← name).toList); isMethod := true; break
      else break
    let (ps, va, b) ← funcBody
    return .assign [target] [.func (if isMethod then "self" :: ps else ps) va b]
  | .kw "local" =>
    advance
    if ← acceptKw "function" then
      let n ← name
      let (ps, va, b) ← funcBody
      return .locfn n ps va b
    let mut ns := #[← name]
    while ← acceptSym "," do ns := ns.push (← name)
    let es ← if ← acceptSym "=" then exprList else pure []
    return .loc ns.toList es
  | _ =>
    let e ← suffixedExp
    if isSym (← peek) "=" || isSym (← peek) "," then
      let mut ts := #[e]
      while ← acceptSym "," do ts := ts.push (← suffixedExp)
      expectSym "="
      return .assign ts.toList (← exprList)
    else match e with
      | .call .. | .method .. => return .call e
      | _ => throw s!"syntax error at {← where_}"
end

end Parser

open Parser in
def parseChunk (src : List Char) : Except String Block := do
  let toks ← lex src #[]
  let (b, s) ← (do let b ← block; pure b : P Block).run { toks, pos := 0 }
  match s.toks.getD s.pos .eof with
  | .eof => return b
  | _ => throw s!"'<eof>' expected at token {s.pos}"

/-- a file's bytes, one `Char` each -/
def bytesOf (b : ByteArray) : List Char := b.toList.map fun x => Char.ofNat x.toNat

end Swarm.Lua
