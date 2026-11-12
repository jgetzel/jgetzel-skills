import LuaLean.Syntax

/-! A parser for the subset: Lua 5.1's grammar and precedence, LuaJIT's lexer (`\x`, `\z`, `\u{...}`), `goto`. It is
not part of what is proved: proofs are about the syntax tree it gives, written out as Lean (`LuaSrc.lean`). -/

namespace Lua

inductive Token where
  | name (s : String) | kw (s : String) | num (n : Num) | cnum (v : Nat) (u : Bool) | str (s : List Char)
  | sym (s : String) | eof
  deriving Inhabited

def keywords : List String :=
  ["and", "break", "do", "else", "elseif", "end", "false", "for", "function", "if", "in", "local", "nil",
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

/-- a newline as LuaJIT's lexer reads one: `\n`, `\r`, or either pair; the rest after it -/
def newline? : List Char → Option (List Char)
  | '\r' :: '\n' :: r | '\n' :: '\r' :: r | '\n' :: r | '\r' :: r => some r
  | _ => none

/-- a long bracket's text up to its close (each newline as `\n`), the rest, and the newlines in it -/
partial def longBody (n : Nat) (s : List Char) (acc : List Char) (nl : Nat := 0) :
    Except String (List Char × List Char × Nat) :=
  match newline? s with
  | some r => longBody n r ('\n' :: acc) (nl + 1)
  | none =>
  match s with
  | [] => .error "unfinished long string"
  | ']' :: r =>
    let k := (r.takeWhile (· == '=')).length
    if k == n && (r.drop k).head? == some ']' then .ok (acc.reverse, r.drop (k + 1), nl)
    else longBody n r (']' :: acc) nl
  | c :: r => longBody n r (c :: acc) nl

def skipFirstNewline (s : List Char) : List Char × Nat :=
  match newline? s with
  | some r => (r, 1)
  | none => (s, 0)

/-- the newlines in whitespace -/
partial def countNl : List Char → Nat
  | [] => 0
  | c :: r => match newline? (c :: r) with
    | some r' => countNl r' + 1
    | none => countNl r

/-- the UTF-8 bytes of a code point, as `\u{...}` writes them -/
def utf8 (v : Nat) : List Char :=
  let b := fun (k : Nat) => 0x80 ||| ((v >>> k) &&& 0x3f)
  (if v < 0x80 then [v] else if v < 0x800 then [0xc0 ||| (v >>> 6), b 0]
   else if v < 0x10000 then [0xe0 ||| (v >>> 12), b 6, b 0] else [0xf0 ||| (v >>> 18), b 12, b 6, b 0]).map Char.ofNat

/-- a quoted string's text up to its close, the rest, and the newlines in it (escaped) -/
partial def quoted (q : Char) (s : List Char) (acc : List Char) (nl : Nat := 0) :
    Except String (List Char × List Char × Nat) :=
  match s with
  | [] => .error "unfinished string"
  | '\n' :: _ | '\r' :: _ => .error "unfinished string"
  | c :: r =>
    if c == q then .ok (acc.reverse, r, nl) else
    if c != '\\' then quoted q r (c :: acc) nl else
    match newline? r with
    | some r => quoted q r ('\n' :: acc) (nl + 1)
    | none =>
    match r with
    | 'n' :: r => quoted q r ('\n' :: acc) nl
    | 't' :: r => quoted q r ('\t' :: acc) nl
    | 'r' :: r => quoted q r ('\r' :: acc) nl
    | 'a' :: r => quoted q r ('\x07' :: acc) nl
    | 'b' :: r => quoted q r ('\x08' :: acc) nl
    | 'f' :: r => quoted q r ('\x0c' :: acc) nl
    | 'v' :: r => quoted q r ('\x0b' :: acc) nl
    | 'x' :: a :: b :: r =>
      match Num.hexVal a, Num.hexVal b with
      | some x, some y => quoted q r (Char.ofNat (16 * x + y) :: acc) nl
      | _, _ => .error "bad \\x escape"
    | 'z' :: r =>
      let ws := r.takeWhile Num.isSpace
      quoted q (r.drop ws.length) acc (nl + countNl ws)
    | 'u' :: '{' :: r =>
      let ds := r.takeWhile fun c => (Num.hexVal c).isSome
      let v := ds.foldl (fun a c => 16 * a + (Num.hexVal c).getD 0) 0
      match r.drop ds.length with
      | '}' :: r =>
        if ds.isEmpty || v ≥ 0x110000 || (0xd800 ≤ v && v < 0xe000) then .error "invalid escape sequence"
        else quoted q r ((utf8 v).reverse ++ acc) nl
      | _ => .error "invalid escape sequence"
    | d :: r =>
      if Num.isDigit d then
        let ds := (d :: r).takeWhile Num.isDigit |>.take 3
        let v := ds.foldl (fun a c => 10 * a + (c.toNat - '0'.toNat)) 0
        if v > 255 then .error "escape too large" else quoted q ((d :: r).drop ds.length) (Char.ofNat v :: acc) nl
      else if d == '\\' || d == '"' || d == '\'' then quoted q r (d :: acc) nl
      else .error "invalid escape sequence"
    | [] => .error "unfinished string"

/-- an FFI numeral (lj_strscan's STRSCAN_OPT_LL): a decimal or hex integer and `LL`, `ULL` or `LLU`, in either
case, below 2^64; its value and whether it is a `uint64_t` -/
def cnumeral (w : List Char) : Option (Nat × Bool) := do
  let l := w.map Num.lower
  let sfx (x : String) := l.drop (l.length - x.length) == x.toList
  let (ds, u) ← if sfx "ull" || sfx "llu" then some (l.take (l.length - 3), true)
    else if sfx "ll" then some (l.take (l.length - 2), false) else none
  let (b, ds) := match ds with | '0' :: 'x' :: r => (16, r) | r => (10, r)
  let (v, n, rest) := Num.spanDigits b ds 0 0
  if n == 0 || !rest.isEmpty || v ≥ 2 ^ 64 then none else some (v, u)

#guard ["1LL", "1ull", "0x10lLU", "18446744073709551615ULL", "00012LL", "0x00000000000000001LL", "1L", "1LLL",
  "1ULLU", "1e2LL", "1.5LL", "0xLL", "18446744073709551616ULL", "0x10000000000000000LL", "2i"].map
  (cnumeral ·.toList) == [some (1, false), some (1, true), some (16, true), some (2 ^ 64 - 1, true), some (12, false),
  some (1, false), none, none, none, none, none, none, none, none, none]

def syms3 : List String := ["..."]
def syms2 : List String := ["==", "~=", "<=", ">=", "..", "::"]
def syms1 : List Char := "+-*/%^#<>=(){}[];:,.".toList

/-- the tokens, each with the line it ends on (LuaJIT's `lastline` once it is read: the line of an instruction) -/
partial def lex (s : List Char) (acc : Array (Token × Nat)) (line : Nat := 1) : Except String (Array (Token × Nat)) :=
  match newline? s with
  | some r => lex r acc (line + 1)
  | none =>
  match s with
  | [] => .ok (acc.push (.eof, line))
  | c :: r =>
    if Num.isSpace c then lex r acc line
    else if c == '-' && r.head? == some '-' then
      let r := r.tail
      match longOpen r with
      | some (n, b) => do let (_, rest, nl) ← longBody n b []; lex rest acc (line + nl)
      | none => lex (r.dropWhile fun c => c != '\n' && c != '\r') acc line
    else if isAlpha c then
      let w := (c :: r).takeWhile isAlnum
      let s := String.ofList w
      lex ((c :: r).drop w.length) (acc.push (if keywords.contains s then .kw s else .name s, line)) line
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
      | some (f, []) => lex rest (acc.push (.num (Num.narrow f), line)) line
      | _ => match cnumeral w with
        | some (v, u) => lex rest (acc.push (.cnum v u, line)) line
        | none => .error s!"malformed number {String.ofList w}"
    else if c == '"' || c == '\'' then do
      let (str, rest, nl) ← quoted c r []
      lex rest (acc.push (.str str, line + nl)) (line + nl)
    else if c == '[' && (longOpen s).isSome then do
      let (n, b) := (longOpen s).get!
      let (b, nl0) := skipFirstNewline b
      let (str, rest, nl) ← longBody n b []
      lex rest (acc.push (.str str, line + nl0 + nl)) (line + nl0 + nl)
    else
      let w3 := String.ofList (s.take 3)
      let w2 := String.ofList (s.take 2)
      if syms3.contains w3 then lex (s.drop 3) (acc.push (.sym w3, line)) line
      else if syms2.contains w2 then lex (s.drop 2) (acc.push (.sym w2, line)) line
      else if syms1.contains c then lex r (acc.push (.sym c.toString, line)) line
      else .error s!"unexpected character {c}"

namespace Parser

structure PState where
  toks : Array Token
  /-- the line each token ends on -/
  lines : Array Nat
  pos : Nat
  /-- the chunk's name, as error messages give it -/
  src : String
  /-- the locals in scope, of each function from the innermost out -/
  fns : List (List String) := [[]]

abbrev P := StateT PState (Except String)

def peek : P Token := do let s ← get; return s.toks.getD s.pos .eof
def peek2 : P Token := do let s ← get; return s.toks.getD (s.pos + 1) .eof
def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

def isSym (t : Token) (x : String) : Bool := match t with | .sym y => x == y | _ => false
def isKw (t : Token) (x : String) : Bool := match t with | .kw y => x == y | _ => false

def where_ : P String := do
  let s ← get
  return s!"line {s.lines.getD s.pos 0} (token {s.pos})"

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

-- ---------- where LuaJIT reports errors ----------

/-- the line of the last token read: LuaJIT gives an instruction the line its parser has read up to -/
def lastLine : P Nat := do let s ← get; return s.lines.getD (s.pos - 1) 1
/-- the line of the token about to be read -/
def curLine : P Nat := do let s ← get; return s.lines.getD s.pos 1

def site (line : Nat) (names : List (String × String) := []) (fn : String × String := ("", "")) : P Site := do
  return { src := (← get).src, line, names, fn }

/-- an operand's name in LuaJIT's messages (lj_debug_slotname): a local, upvalue or global, or a field read with a
constant string key -/
partial def desc : Exp → P (String × String)
  | .var x => do
    match (← get).fns with
    | cur :: outer =>
      return if cur.contains x then ("local", x) else if outer.any (·.contains x) then ("upvalue", x) else ("global", x)
    | [] => return ("global", x)
  | .site _ (.index _ (.str k)) => return ("field", String.ofList k)
  | .paren e => desc e
  | _ => return ("", "")

/-- LuaJIT emits a table read when the next operation needs its value: past the operator after it, or the `,` or
`)` after it, the read gets that token's line -/
def readAt (line : Nat) : Exp → Exp
  | .site s (.index t k) => .site { s with line } (.index t k)
  | e => e

def bindLocal (x : String) : P Unit := modify fun s =>
  { s with fns := match s.fns with | cur :: outer => (x :: cur) :: outer | [] => [[x]] }

/-- `p` in a scope of its own: the locals it declares end with it -/
def inScope {α} (p : P α) : P α := do
  let saved := (← get).fns
  let r ← p
  modify fun s => { s with fns := saved }
  return r

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
def fold (o : BinOp) (a b : Exp) : Option Exp :=
  let k := match o with
    | .add => some 0 | .sub => some 1 | .mul => some 2 | .div => some 3 | .mod => some 4 | .pow => some 5
    | _ => none
  match k, a, b with
  | some k, .num x, .num y => (Num.foldArith k x y).map .num
  | _, _, _ => none

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
      | .num k => match Num.foldNeg k with
        | some k => pure (Exp.num k)
        | none => pure (.site (← site (← lastLine)) (Exp.un .neg (.num k)))
      | e => pure (.site (← site (← lastLine) [← desc e]) (Exp.un .neg e))
    else if isSym t "#" then do advance; let e ← expr 8; pure (.site (← site (← lastLine) [← desc e]) (Exp.un .len e))
    else simpleExp
  repeat
    let (op, l, r) := binop (← peek)
    match op with
    | some o =>
      if l > limit then
        advance
        e := readAt (← lastLine) e
        let b ← expr r
        e ← match o with
          | .inl o => match fold o e b with
            | some k => pure k
            | none =>
              -- == and ~= raise no error
              if o == .eq || o == .ne then pure (.bin o e b)
              -- one CAT for `a .. b .. c`: `b .. c`'s value, from a metamethod, sits in b's slot, named b's
              else if let (.concat, .site _ (.bin .concat b1 _)) := (o, b) then do
                pure (.site (← site (← lastLine) [← desc e, ← desc b1]) (.bin o e b))
              else do pure (.site (← site (← lastLine) [← desc e, ← desc b]) (.bin o e b))
          | .inr true => pure (.and e b)
          | .inr false => pure (.or e b)
      else break
    | none => break
  return e

partial def simpleExp : P Exp := do
  match ← peek with
  | .num n => advance; return .num n
  | .cnum v u => advance; return .cnum v u
  | .str s => advance; return .str s
  | .kw "nil" => advance; return .nil
  | .kw "true" => advance; return .tru
  | .kw "false" => advance; return .fls
  | .sym "..." => advance; return .vararg
  | .sym "{" => tableCons
  | .kw "function" => let l ← curLine; advance; let (ps, va, b, e) ← funcBody false; return .func ps va b (l, e)
  | _ => suffixedExp

partial def primaryExp : P Exp := do
  match ← peek with
  | .name n => advance; return .var n
  | .sym "(" =>
    advance; let e ← expr; expectSym ")"
    return (match readAt (← lastLine) e with | .num k => .num k | e => .paren e)
  | _ => throw s!"unexpected symbol at {← where_}"

partial def suffixedExp : P Exp := do
  let mut e ← primaryExp
  repeat
    let t ← peek
    if isSym t "." then
      -- the table before `.` is read once the `.` is (lj_parse.c's expr_primary_nav)
      advance; e := readAt (← lastLine) e; let k := (← name).toList
      e := .site (← site (← lastLine) [← desc e]) (.index e (.str k))
    else if isSym t "[" then
      advance; let k ← expr; expectSym "]"
      e := .site (← site (← lastLine) [← desc e]) (.index e k)
    else if isSym t ":" then
      advance; let n ← name
      e := readAt (← lastLine) e
      let s ← site (← curLine) [← desc e] ("method", n)
      e := .site s (.method e n (← callArgs))
    else if isSym t "(" || isSym t "{" || (match t with | .str _ => true | _ => false) then
      let s ← site (← curLine) [] (← desc e)
      e := .site s (.call e (← callArgs))
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
    let l ← lastLine
    return es.dropLast ++ (es.getLast?.map (readAt l)).toList

partial def exprList : P (List Exp) := do
  let mut es := #[← expr]
  while ← acceptSym "," do
    let l ← lastLine
    es := es.modify (es.size - 1) (readAt l)
    es := es.push (← expr)
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

/-- a function's parameters and body, in a scope of its own (`self` first for a method), and the line of its `end` -/
partial def funcBody (self : Bool) : P (List String × Bool × Block × Nat) := do
  expectSym "("
  let mut ps : Array String := #[]
  let mut va := false
  if !(isSym (← peek) ")") then
    repeat
      if ← acceptSym "..." then va := true; break
      ps := ps.push (← name)
      if !(← acceptSym ",") then break
  expectSym ")"
  let params := (if self then ["self"] else []) ++ ps.toList
  let saved := (← get).fns
  modify fun s => { s with fns := params.reverse :: s.fns }
  let b ← blockIn
  modify fun s => { s with fns := saved }
  let e ← curLine
  expectKw "end"
  return (params, va, b, e)

partial def block : P Block := inScope blockIn

/-- a block's statements, its locals left in scope (a `repeat`'s condition sees them) -/
partial def blockIn : P Block := do
  let mut ss : Array Stat := #[]
  repeat
    let t ← peek
    if blockEnd t then break
    if isKw t "return" then
      advance
      let es ← if blockEnd (← peek) || isSym (← peek) ";" then pure [] else exprList
      -- `return f(...)` is a tail call: CALLT is emitted anew once the call is read (parse_return)
      let l ← lastLine
      let es := match es with
        | [.site s (.call f as)] => [.site { s with tail := true, line := l } (.call f as)]
        | [.site s (.method o m as)] => [.site { s with tail := true, line := l } (.method o m as)]
        | es => es
      ss := ss.push (.ret es)
      while ← acceptSym ";" do pure ()
      break
    if ← acceptSym ";" then continue
    let st ← stat
    ss := ss.push st
    -- `break` ends its block, as `return` does (LuaJIT's parse_chunk): only `;`s may follow
    if st matches .brk then
      while ← acceptSym ";" do pure ()
      break
  return ss.toList

/-- an assignment target: a table write is reported on `line` -/
partial def target (line : Nat) : Exp → Exp
  | .site s (.index t k) => .site { s with line } (.index t k)
  | e => e

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
  | .kw "repeat" =>
    advance
    inScope do
      let b ← blockIn; expectKw "until"
      return .rpt b (← expr)
  | .kw "break" => advance; return .brk
  -- `goto` is a soft keyword (LuaJIT without 5.2 compatibility): a statement only when a name follows it
  | .name "goto" => if let .name l := ← peek2 then advance; advance; return .goto l else assignOrCall
  | .sym "::" => advance; let n ← name; expectSym "::"; return .label n
  | .kw "for" =>
    advance
    let n ← name
    if ← acceptSym "=" then
      let a ← expr; expectSym ","; let b ← expr
      let st ← if ← acceptSym "," then some <$> expr else pure none
      expectKw "do"
      -- FORI, which checks the three, is on the line of `do`
      let s ← site (← lastLine)
      let body ← inScope do bindLocal n; block
      expectKw "end"
      return .site s (.fornum n a b st body)
    else
      let mut ns := #[n]
      while ← acceptSym "," do ns := ns.push (← name)
      expectKw "in"
      -- ITERC is on the line the token after `in` ends on (parse_for_iter)
      let forLine ← curLine
      let es ← exprList
      expectKw "do"
      let body ← inScope do ns.forM bindLocal; block
      expectKw "end"
      -- a builtin ITERC calls is named after the hidden local holding it
      return .site (← site forLine [("", "")] ("local", "(for generator)")) (.forin ns.toList es body)
  | .kw "function" =>
    let fnLine ← curLine
    advance
    let n ← name
    let mut target : Exp := .var n
    let mut isMethod := false
    repeat
      if ← acceptSym "." then
        target := readAt (← lastLine) target
        let k := (← name).toList
        target := .site (← site (← lastLine) [← desc target]) (.index target (.str k))
      else if ← acceptSym ":" then
        target := readAt (← lastLine) target
        let k := (← name).toList
        target := .site (← site (← lastLine) [← desc target]) (.index target (.str k)); isMethod := true; break
      else break
    let (ps, va, b, e) ← funcBody isMethod
    -- the store is on the line of `function` (parse_func)
    return .assign [Parser.target fnLine target] [.func ps va b (fnLine, e)]
  | .kw "local" =>
    advance
    let l ← curLine
    if ← acceptKw "function" then
      let n ← name
      bindLocal n
      let (ps, va, b, e) ← funcBody false
      return .locfn n ps va b (l, e)
    let mut ns := #[← name]
    while ← acceptSym "," do ns := ns.push (← name)
    let es ← if ← acceptSym "=" then exprList else pure []
    ns.forM bindLocal
    return .loc ns.toList es
  | _ => assignOrCall

partial def assignOrCall : P Stat := do
  let e ← suffixedExp
  if isSym (← peek) "=" || isSym (← peek) "," then
    let mut ts := #[e]
    while ← acceptSym "," do ts := ts.push (← suffixedExp)
    -- a name or an index, as lj_parse.c's parse_assignment checks: not `(x)`, `f()`, `o:m()`
    unless ts.all (fun | .var _ | .site _ (.index ..) => true | _ => false) do throw s!"syntax error at {← where_}"
    expectSym "="
    let es ← exprList
    -- the stores come after the values: on the line the list ends
    let l ← lastLine
    return .assign (ts.toList.map (target l)) es
  else match e with
    | .site _ (.call ..) | .site _ (.method ..) => return .call e
    | _ => throw s!"syntax error at {← where_}"
end

end Parser

open Parser in
/-- the file's syntax tree; `src` names the chunk in its error messages, as LuaJIT's chunkname (without its `@`
or `=`) -/
def parseChunk (src : List Char) (chunk : String) : Except String Block := do
  let toks ← lex src #[]
  let (b, s) ← (do let b ← blockIn; pure b : P Block).run
    { toks := toks.map (·.1), lines := toks.map (·.2), pos := 0, src := chunk }
  match s.toks.getD s.pos .eof with
  | .eof => return b
  | _ => throw s!"'<eof>' expected at token {s.pos}"

open Parser in
/-- the line a chunk's source ends on: its function's lastlinedefined, LuaJIT's line number when the parse ends -/
def chunkLines (src : List Char) : Nat :=
  match lex src #[] with
  | .ok toks => (toks.back?.map (·.2)).getD 1
  | .error _ => 1

/-- a file's bytes, one `Char` each -/
def bytesOf (b : ByteArray) : List Char := b.toList.map fun x => Char.ofNat x.toNat

end Lua
