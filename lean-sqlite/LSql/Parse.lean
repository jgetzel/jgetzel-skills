import LSql.Ast
import LSql.Lex
/-! The SQL parser: recursive descent over the tokens of LSql.Lex, producing LSql.Ast. Precedence follows parse.y's %left table;
keywords usable as identifiers follow %fallback ID. Every recursive function is fuel-bounded (fuel = 8 * input bytes + 64, more than
the call depth any input can reach), so none is partial. -/
namespace LSql.Parse
open LSql LSql.Lex

structure ParseError where
  /-- sqlite's message text. -/
  msg : String
  /-- Byte offset of the offending token. -/
  pos : Nat
  deriving Repr, Inhabited

structure PS where
  src : String
  tok : Token
  prevEnd : Nat
  /-- The named windows in scope (newest first); consulted when `resolve`. -/
  wins : List (String × Window) := []
  /-- False while a SELECT core is parsed the first time: a window name is not known yet, so it is recorded in `named`. -/
  resolve : Bool := false
  named : Bool := false
  /-- An error sqlite reports only if the rest of the statement parses (a later syntax error replaces it). -/
  late : Option ParseError := none
  /-- The object name of the CREATE being parsed was qualified `temp.`. -/
  tmpName : Bool := false

abbrev P := StateT PS (Except ParseError)

/-! ## Token access -/

@[inline] def curTok : P Token := fun st => .ok (st.tok, st)
@[inline] def curKind : P TK := fun st => .ok (st.tok.kind, st)
@[inline] def peek1 : P Token := fun st => .ok (lexTok st.src st.tok.e, st)

def advance : P Unit := fun st =>
  let t := lexTok st.src st.tok.e
  if t.kind == .illegal then .error ⟨s!"unrecognized token: \"{sub st.src t.s t.e}\"", t.s⟩
  else .ok ((), { st with tok := t, prevEnd := st.tok.e })

def synErr {α : Type} : P α := fun st =>
  let t := st.tok
  if t.kind == .eof then .error ⟨"incomplete input", t.s⟩
  else .error ⟨s!"near \"{sub st.src t.s t.e}\": syntax error", t.s⟩

def unsupported {α : Type} (what : String) : P α := fun st =>
  .error ⟨s!"lean-sqlite: unsupported: {what}", st.tok.s⟩

def deferErr (msg : String) (pos : Nat) : P Unit :=
  modify fun st => if st.late.isNone then { st with late := some ⟨msg, pos⟩ } else st

/-- sqlite's tokenizer reads WINDOW as a keyword only before `name AS`. -/
def isWindowClauseAt (st : PS) : Bool :=
  st.tok.kind == .kWINDOW &&
    (let n1 := lexTok st.src st.tok.e
     (n1.kind == .id || n1.kind == .qid || n1.kind == .dqid) && (lexTok st.src n1.e).kind == .kAS)

/-- ... OVER only before `(` or a name, after a ')'. -/
def isOverAt (st : PS) : Bool :=
  st.tok.kind == .kOVER &&
    (let n1 := lexTok st.src st.tok.e
     n1.kind == .lp || n1.kind == .id || n1.kind == .qid || n1.kind == .dqid)

def errAt {α : Type} (msg : String) (pos : Nat) : P α := fun _ => .error ⟨msg, pos⟩

def expect (k : TK) : P Unit := do
  if (← curKind) == k then advance else synErr

def accept (k : TK) : P Bool := do
  if (← curKind) == k then advance; return true else return false

def liftE {α : Type} (r : Except ParseError α) : P α := fun st =>
  match r with
  | .ok a => .ok (a, st)
  | .error e => .error e

/-- Text of a name token with its quotes removed (a doubled quote stands for one). -/
def unquoteFrom (src : String) (q : UInt8) (e : Nat) (i : Nat) (acc : String) : Nat → String
  | 0 => acc
  | f + 1 =>
    let j := scanWhile (· != q) src i
    if j >= e then acc ++ sub src i e
    else unquoteFrom src q e (j + 2) (acc ++ sub src i (j + 1)) f

def nameOf (src : String) (t : Token) : String :=
  match byteAt src t.s with
  | 34 | 96 | 39 =>
    let s := t.s + 1
    let e := t.e - 1
    if scanWhile (· != byteAt src t.s) src s >= e then sub src s e
    else unquoteFrom src (byteAt src t.s) e s "" (e - s + 1)
  | 91 => sub src (t.s + 1) (t.e - 1)
  | _ => sub src t.s t.e

def isIdKind (k : TK) : Bool := k == .id || k == .qid || k == .dqid || k.isFallback
def isNmKind (k : TK) : Bool := isIdKind k || k == .str || k.isJoinKw

def parseNm : P String := fun st =>
  if isNmKind st.tok.kind then
    match advance st with
    | .ok (_, st') => .ok (nameOf st.src st.tok, st')
    | .error e => .error e
  else synErr st

/-- [schema.]name: the last name and the offset where it starts. -/
def parseQName : P (String × Nat) := do
  let t ← curTok
  let n1 ← parseNm
  if (← curKind) == .dot then
    advance
    let t2 ← curTok
    let n2 ← parseNm
    return (n2, t2.s)
  else return (n1, t.s)

namespace Schema'
/-- A name without its `main.`/`temp.` qualifier. -/
def bare (n : String) : String := if n.startsWith "\x00" then ((n.splitOn "\x00").getLast?).getD n else n
end Schema'

/-- A reference [schema.]name: a `main.` or `temp.` qualifier is kept, as the name wrapped in NULs with the schema
(`"\x00temp\x00t"`), which the schema lookups read; another qualifier is dropped. -/
def parseQNameM : P (String × Nat) := do
  let t ← curTok
  let n1 ← parseNm
  if (← curKind) == .dot then
    advance
    let t2 ← curTok
    let n2 ← parseNm
    let q := n1.toLower
    if q == "main" || q == "temp" then return ("\x00" ++ q ++ "\x00" ++ n2, t2.s)
    return (n2, t2.s)
  else return (n1, t.s)

/-- [schema.]name for a CREATE: the last name, the offset where it starts, and the schema name (when written). -/
def parseQNameS : P (String × Nat × Option String) := do
  let t ← curTok
  let n1 ← parseNm
  if (← curKind) == .dot then
    advance
    let t2 ← curTok
    let n2 ← parseNm
    return (n2, t2.s, some n1)
  else return (n1, t.s, none)

def isTempSchema (s : String) : Bool := s.toLower == "temp"

/-- The name of a CREATE TABLE/VIEW/TRIGGER: records `temp.`, and refuses another schema under CREATE TEMP. -/
def parseCreateName (isTemp : Bool) (what : String) : P (String × Nat) := do
  let pos := (← curTok).s
  let (n, st, sch) ← parseQNameS
  match sch with
  | some sc =>
    if isTempSchema sc then modify fun s => { s with tmpName := true }
    else if isTemp then errAt what pos
  | none => pure ()
  return (n, st)

def fuelOf : P Nat := fun st => .ok (st.src.utf8ByteSize * 8 + 64, st)

/-! ## Literals -/

def decAcc (src : String) (e : Nat) (i : Nat) (acc : UInt64) (ovf : Bool) : Nat → UInt64 × Bool
  | 0 => (acc, ovf)
  | f + 1 =>
    if i >= e then (acc, ovf) else
    let c := byteAt src i
    if c == 95 then decAcc src e (i + 1) acc ovf f
    else
      let d := (c - 48).toUInt64
      if acc > 1844674407370955161 || (acc == 1844674407370955161 && d > 5) then decAcc src e (i + 1) acc true f
      else decAcc src e (i + 1) (acc * 10 + d) ovf f

/-- Mantissa digits (with the '.'), as (mantissa, number of fraction digits, index after). -/
def mantissa (src : String) (e : Nat) (i : Nat) (m : Nat) (frac : Nat) (dot : Bool) : Nat → Nat × Nat × Nat
  | 0 => (m, frac, i)
  | f + 1 =>
    if i >= e then (m, frac, i) else
    let c := byteAt src i
    if isDigit c then mantissa src e (i + 1) (m * 10 + (c - 48).toNat) (if dot then frac + 1 else frac) dot f
    else if c == 95 then mantissa src e (i + 1) m frac dot f
    else if c == 46 then mantissa src e (i + 1) m frac true f
    else (m, frac, i)

def expDigits (src : String) (e : Nat) (i : Nat) (acc : Nat) : Nat → Nat
  | 0 => acc
  | f + 1 =>
    if i >= e then acc else
    let c := byteAt src i
    if isDigit c then expDigits src e (i + 1) (min 100000 (acc * 10 + (c - 48).toNat)) f
    else expDigits src e (i + 1) acc f

/-- The Float of a decimal literal in bytes [s, e), correctly rounded. -/
def realOf (src : String) (s e : Nat) : Float :=
  let (m, frac, i) := mantissa src e s 0 0 false (e - s + 1)
  let (neg, ex) :=
    if i < e && (byteAt src i ||| 32) == 101 then
      let sg := byteAt src (i + 1)
      if sg == 45 then (true, expDigits src e (i + 2) 0 (e - i))
      else if sg == 43 then (false, expDigits src e (i + 2) 0 (e - i))
      else (false, expDigits src e (i + 1) 0 (e - i))
    else (false, 0)
  let exp10 : Int := (if neg then -(ex : Int) else (ex : Int)) - frac
  if m == 0 then 0.0
  else if exp10 > 330 then Float.ofScientific 1 false 400
  else if exp10 >= 0 then Float.ofScientific m false exp10.toNat
  else if (-exp10).toNat > (e - s) + 330 then 0.0
  else Float.ofScientific m true (-exp10).toNat

def hexVal (c : UInt8) : UInt8 := if c <= 57 then c - 48 else (c ||| 32) - 87

def hexAcc (src : String) (e : Nat) (i : Nat) (acc : UInt64) (cnt : Nat) : Nat → UInt64 × Nat
  | 0 => (acc, cnt)
  | f + 1 =>
    if i >= e then (acc, cnt) else
    let c := byteAt src i
    if c == 95 then hexAcc src e (i + 1) acc cnt f
    else hexAcc src e (i + 1) (acc * 16 + (hexVal c).toUInt64) (if cnt > 0 || c != 48 then cnt + 1 else cnt) f

def blobOf (src : String) (s e : Nat) : ByteArray :=
  go s ByteArray.empty (e - s)
where
  go (i : Nat) (acc : ByteArray) : Nat → ByteArray
    | 0 => acc
    | f + 1 =>
      if i + 1 >= e then acc
      else go (i + 2) (acc.push (hexVal (byteAt src i) * 16 + hexVal (byteAt src (i + 1)))) f

/-- A numeric literal token as an expression. -/
def litOfTok (src : String) (t : Token) : Except ParseError Expr :=
  match t.kind with
  | .int =>
    let (v, ovf) := decAcc src t.e t.s 0 false (t.e - t.s + 1)
    if !ovf && v < 0x8000000000000000 then .ok (.lit (.int v.toInt64))
    else .ok (.lit (.real (realOf src t.s t.e)))
  | .real => .ok (.lit (.real (realOf src t.s t.e)))
  | .hex =>
    let (v, cnt) := hexAcc src t.e (t.s + 2) 0 0 (t.e - t.s + 1)
    if cnt > 16 then .error ⟨s!"hex literal too big: {sub src t.s t.e}", t.s⟩
    else .ok (.lit (.int v.toInt64))
  | _ => .error ⟨"not a number", t.s⟩

/-- The integer token 9223372036854775808 (valid only under a unary minus). -/
def isMinMag (src : String) (t : Token) : Bool :=
  t.kind == .int &&
    (let (v, ovf) := decAcc src t.e t.s 0 false (t.e - t.s + 1)
     !ovf && v == 0x8000000000000000)

def int64Min : Value := .int (0x8000000000000000 : UInt64).toInt64

def isTrueFalse (src : String) (t : Token) : Option Int64 :=
  if t.kind != .id then none
  else if t.e - t.s == 4 && eqFold "TRUE" src t.s 4 then some 1
  else if t.e - t.s == 5 && eqFold "FALSE" src t.s 5 then some 0
  else none

/-! ## Type names, aliases, small clauses -/

/-- [+-] number, as part of a type name's size. -/
def skipSigned : P Unit := do
  let k ← curKind
  if k == .plus || k == .minus then advance
  let k ← curKind
  if k == .int || k == .real || k == .hex then advance else synErr

/-- A column's declared type (or a CAST's): the source text from its first token to its last; "" when absent. -/
def parseTypeName : P String := do
  let t0 ← curTok
  let n ← fuelOf
  let mut any := false
  for _ in [0:n] do
    let k ← curKind
    if (isIdKind k || k == .str) && k != .kGENERATED then
      advance
      any := true
    else break
  if !any then return ""
  if (← curKind) == .lp then
    advance
    skipSigned
    if (← curKind) == .comma then
      advance
      skipSigned
    expect .rp
  let st ← get
  return sub st.src t0.s st.prevEnd

/-- [AS] alias after a result column or a table. -/
def parseAlias : P (Option String) := do
  let st ← get
  let k := st.tok.kind
  if k == .kAS then
    advance
    return some (← parseNm)
  else if (isIdKind k || k == .str) && !(k == .kINDEXED && (lexTok st.src st.tok.e).kind == .kBY) && !isWindowClauseAt st then
    advance
    return some (nameOf st.src st.tok)
  else return none

def nmListAux : Nat → List String → P (List String)
  | 0, _ => synErr
  | f + 1, acc => do
    let n ← parseNm
    if (← curKind) == .comma then
      advance
      nmListAux f (n :: acc)
    else return (n :: acc).reverse

def nmList : P (List String) := do nmListAux (← fuelOf) []

def tableSelect (name : String) : Select :=
  .mk false [] (.select false [.star] (some (.table name none)) [] none [] none) [] [] none none

def isSelectStart (k : TK) : Bool := k == .kSELECT || k == .kWITH || k == .kVALUES

def infixOp : TK → Option (Nat × BinOp)
  | .kOR => some (1, .or)
  | .kAND => some (2, .and)
  | .eq => some (4, .eq)
  | .ne => some (4, .ne)
  | .lt => some (5, .lt)
  | .le => some (5, .le)
  | .gt => some (5, .gt)
  | .ge => some (5, .ge)
  | .bitand => some (7, .bitAnd)
  | .bitor => some (7, .bitOr)
  | .shl => some (7, .shl)
  | .shr => some (7, .shr)
  | .plus => some (8, .add)
  | .minus => some (8, .sub)
  | .star => some (9, .mul)
  | .slash => some (9, .div)
  | .rem => some (9, .mod)
  | .concat => some (10, .concat)
  | _ => none

/-! ## Windows and joins -/

def badFrame : FrameBound → FrameBound → Bool
  | .currentRow, .preceding _ => true
  | .following _, .preceding _ => true
  | .following _, .currentRow => true
  | _, _ => false

def offsetBound : FrameBound → Bool
  | .preceding _ => true
  | .following _ => true
  | _ => false

def lowerEq (a b : String) : Bool := a.toLower == b.toLower

def findWin (wins : List (String × Window)) (n : String) : Option Window :=
  (wins.find? fun p => lowerEq p.1 n).map (·.2)

/-- The named window `n`, or none while the SELECT core is parsed the first time (the name is then only recorded). -/
def resolveBase (n : String) (pos : Nat) : P (Option Window) := do
  let st ← get
  if !st.resolve then
    set { st with named := true }
    return none
  else
    match findWin st.wins n with
    | some w => return some w
    | none => errAt s!"no such window: {n}" pos

/-- A window `(base [PARTITION BY ..] [ORDER BY ..] [frame])` merged with its base as sqlite3WindowChain does; the flag: the
base is not known yet. -/
def mergeBase (n : String) (pos : Nat) (part : List Expr) (ob : List OrderTerm) (fr : Option Frame) : P (Window × Bool) := do
  match ← resolveBase n pos with
  | none => return (Window.mk part ob fr, true)
  | some (.mk bp bo bf) =>
    if !part.isEmpty then errAt s!"cannot override PARTITION clause of window: {n}" pos
    else if !bo.isEmpty && !ob.isEmpty then errAt s!"cannot override ORDER BY clause of window: {n}" pos
    else if bf.isSome then errAt s!"cannot override frame specification of window: {n}" pos
    else return (Window.mk bp (if bo.isEmpty then ob else bo) fr, false)

def checkRange (w : Window) (pos : Nat) : P Unit :=
  match w with
  | .mk _ ob (some (.mk .range s e _)) =>
    if (offsetBound s || offsetBound e) && ob.length != 1 then
      errAt "RANGE with offset PRECEDING/FOLLOWING requires one ORDER BY expression" pos
    else pure ()
  | _ => pure ()

def windowOnlyFns : List String :=
  ["row_number", "rank", "dense_rank", "percent_rank", "cume_dist", "ntile", "lag", "lead", "first_value", "last_value", "nth_value"]

/-- sqlite3JoinType's bits: NATURAL 1, INNER 2, CROSS 4, LEFT 8, RIGHT 16, OUTER 32; 0 for a word that is no join keyword. -/
def joinWordBits : TK → Nat
  | .kNATURAL => 1
  | .kINNER => 2
  | .kCROSS => 6
  | .kLEFT => 40
  | .kRIGHT => 48
  | .kFULL => 56
  | .kOUTER => 32
  | _ => 0

/-- The words of a join operator (JOIN_KW [nm [nm]] JOIN, the current token being the first) up to and including JOIN, read as
sqlite3JoinType does: the kind and whether it is NATURAL. -/
def joinOp : P (JoinKind × Bool) := do
  let st ← get
  let t0 := st.tok
  let mut jt : Nat := 0
  let mut bad := false
  let mut texts : Array String := #[]
  for _ in [0:3] do
    let t ← curTok
    if t.kind == .kJOIN || !isNmKind t.kind then break
    let b := joinWordBits t.kind
    if b == 0 then bad := true
    jt := jt ||| b
    texts := texts.push (sub st.src t.s t.e)
    advance
  expect .kJOIN
  if bad || (jt &&& 2 != 0 && jt &&& 32 != 0) || (jt &&& 32 != 0 && jt &&& 24 == 0) then
    errAt s!"unknown join type: {" ".intercalate texts.toList}" t0.s
  let natural := jt &&& 1 != 0
  let kind : JoinKind :=
    if jt &&& 4 != 0 then (if natural then .inner else .cross)
    else if jt &&& 8 != 0 && jt &&& 16 != 0 then .full
    else if jt &&& 16 != 0 then .right
    else if jt &&& 8 != 0 then .left
    else .inner
  return (kind, natural)

/-! ## Expressions and SELECT -/

mutual

def parseBin : Nat → Nat → P Expr
  | 0, _ => synErr
  | f + 1, minP => do
    let lhs ← parseOperand f
    binLoop f minP lhs

def parseExpr : Nat → P Expr
  | 0 => synErr
  | f + 1 => parseBin f 0

def parseOperand : Nat → P Expr
  | 0 => synErr
  | f + 1 => do
    let e ← parseUnary f
    collateLoop f e

def notExpr : Nat → P Expr
  | 0 => synErr
  | f + 1 => do
    advance
    let e ← parseBin f 4
    match e with
    | .exists q false => return .exists q true
    | _ => return .un .not e

def collateLoop : Nat → Expr → P Expr
  | 0, e => return e
  | f + 1, e => do
    if (← curKind) == .kCOLLATE then
      advance
      let n ← parseNm
      collateLoop f (.collate e n)
    else return e

def parseUnary : Nat → P Expr
  | 0 => synErr
  | f + 1 => do
    let st ← get
    match st.tok.kind with
    | .minus =>
      advance
      let nt ← curTok
      if isMinMag st.src nt then
        advance
        return .lit int64Min
      else
        return .un .neg (← parseUnary f)
    | .plus => advance; return .un .pos (← parseUnary f)
    | .bitnot => advance; return .un .bitNot (← parseUnary f)
    | .kNOT => notExpr f
    | _ => parsePrimary f

def binLoop : Nat → Nat → Expr → P Expr
  | 0, _, _ => synErr
  | f + 1, minP, lhs => do
    let k ← curKind
    match infixOp k with
    | some (p, op) =>
      if p < minP then return lhs
      else
        advance
        let r ← parseBin f (p + 1)
        binLoop f minP (.bin op lhs r)
    | none =>
      match k with
      | .ptr | .ptr2 =>
        if 10 < minP then return lhs
        else
          advance
          let r ← parseBin f 11
          binLoop f minP (.fn (if k == .ptr then "->" else "->>") false false [lhs, r])
      | .kIS | .kISNULL | .kNOTNULL | .kBETWEEN | .kIN | .kLIKE | .kGLOB | .kREGEXP | .kMATCH =>
        if 4 < minP then return lhs
        else
          let e ← predicate f lhs false
          binLoop f minP e
      | .kNOT =>
        if 4 < minP then return lhs
        else
          let n ← peek1
          match n.kind with
          | .kNULL =>
            advance
            advance
            binLoop f minP (.isNull lhs true)
          | .kBETWEEN | .kIN | .kLIKE | .kGLOB | .kREGEXP | .kMATCH =>
            advance
            let e ← predicate f lhs true
            binLoop f minP e
          | _ => return lhs
      | _ => return lhs

/-- IS, BETWEEN, IN, LIKE and friends, ISNULL/NOTNULL, after the optional NOT. -/
def predicate : Nat → Expr → Bool → P Expr
  | 0, _, _ => synErr
  | f + 1, lhs, neg => do
    let k ← curKind
    advance
    match k with
    | .kISNULL => return .isNull lhs false
    | .kNOTNULL => return .isNull lhs true
    | .kIS =>
      let n ← accept .kNOT
      let d ← accept .kDISTINCT
      if d then expect .kFROM
      let r ← parseBin f 5
      return .bin (if n != d then .isNot else .is) lhs r
    | .kBETWEEN =>
      let lo ← parseBin f 5
      expect .kAND
      let hi ← parseBin f 5
      return .between lhs lo hi neg
    | .kIN =>
      if (← curKind) == .lp then
        advance
        let k2 ← curKind
        if isSelectStart k2 then
          let q ← parseSelect f
          expect .rp
          return .inSelect lhs q neg
        else if k2 == .rp then
          advance
          return .inList lhs [] neg
        else
          let items ← parseExprList f
          expect .rp
          return .inList lhs items neg
      else
        let (name, _) ← parseQNameM
        return .inSelect lhs (tableSelect name) neg
    | _ =>
      let op : MatchOp := match k with
        | .kLIKE => .like
        | .kGLOB => .glob
        | .kREGEXP => .regexp
        | _ => .«match»
      let pat ← parseBin f 5
      let esc ← if (← curKind) == .kESCAPE then do
          advance
          pure (some (← parseBin f 7))
        else pure none
      return .matches op lhs pat esc neg

def exprRest : Nat → List Expr → P (List Expr)
  | 0, _ => synErr
  | f + 1, acc => do
    if (← curKind) == .comma then
      advance
      let e ← parseExpr f
      exprRest f (e :: acc)
    else return acc.reverse

def parseExprList : Nat → P (List Expr)
  | 0 => synErr
  | f + 1 => do
    let e ← parseExpr f
    exprRest f [e]

def caseWhens : Nat → List (Expr × Expr) → P (List (Expr × Expr))
  | 0, _ => synErr
  | f + 1, acc => do
    if (← curKind) == .kWHEN then
      advance
      let w ← parseExpr f
      expect .kTHEN
      let t ← parseExpr f
      caseWhens f ((w, t) :: acc)
    else if acc.isEmpty then synErr else return acc.reverse

def frameBound : Nat → Bool → P FrameBound
  | 0, _ => synErr
  | f + 1, isStart => do
    match ← curKind with
    | .kUNBOUNDED =>
      advance
      if isStart then
        expect .kPRECEDING
        return .unboundedPreceding
      else
        expect .kFOLLOWING
        return .unboundedFollowing
    | .kCURRENT =>
      advance
      expect .kROW
      return .currentRow
    | _ =>
      let e ← parseExpr f
      match ← curKind with
      | .kPRECEDING => advance; return .preceding e
      | .kFOLLOWING => advance; return .following e
      | _ => synErr

/-- [ROWS|RANGE|GROUPS bound | BETWEEN bound AND bound] [EXCLUDE ..]; none when no frame is written. -/
def parseFrame : Nat → P (Option Frame)
  | 0 => synErr
  | f + 1 => do
    let units? : Option FrameUnits := match ← curKind with
      | .kROWS => some .rows
      | .kRANGE => some .range
      | .kGROUPS => some .groups
      | _ => none
    match units? with
    | none => return none
    | some u =>
      let ft ← curTok
      advance
      let (s, e) ← if (← curKind) == .kBETWEEN then do
          advance
          let s ← frameBound f true
          expect .kAND
          let e ← frameBound f false
          pure (s, e)
        else do
          let s ← frameBound f true
          pure (s, FrameBound.currentRow)
      if badFrame s e then errAt "unsupported frame specification" ft.s
      let exc ← if (← curKind) == .kEXCLUDE then do
          advance
          match ← curKind with
          | .kNO => advance; expect .kOTHERS; pure FrameExclude.noOthers
          | .kCURRENT => advance; expect .kROW; pure FrameExclude.currentRow
          | .kGROUP => advance; pure FrameExclude.group
          | .kTIES => advance; pure FrameExclude.ties
          | _ => synErr
        else pure FrameExclude.noOthers
      return some (Frame.mk u s e exc)

/-- The inside of a window's parentheses: [base] [PARTITION BY ..] [ORDER BY ..] [frame]; the base's name and offset. -/
def windowSpecParts : Nat → P (Option (String × Nat) × List Expr × List OrderTerm × Option Frame)
  | 0 => synErr
  | f + 1 => do
    let k ← curKind
    let bt ← curTok
    let base ← if isNmKind k && k != .kPARTITION && k != .kROWS && k != .kRANGE && k != .kGROUPS then do
        let n ← parseNm
        pure (some (n, bt.s))
      else pure none
    let part ← if (← curKind) == .kPARTITION then do
        advance
        expect .kBY
        parseExprList f
      else pure []
    let ob ← if (← curKind) == .kORDER then do
        advance
        expect .kBY
        orderTerms f []
      else pure []
    let fr ← parseFrame f
    return (base, part, ob, fr)

/-- `OVER (spec)` or `OVER name`; the current token is OVER. -/
def parseOver : Nat → P Window
  | 0 => synErr
  | f + 1 => do
    advance
    if (← curKind) == .lp then
      advance
      let (base, part, ob, fr) ← windowSpecParts f
      let rt ← curTok
      expect .rp
      match base with
      | none =>
        let w : Window := .mk part ob fr
        checkRange w rt.s
        return w
      | some (n, pos) =>
        let (w, ph) ← mergeBase n pos part ob fr
        if !ph then checkRange w pos
        return w
    else
      let nt ← curTok
      let n ← parseNm
      match ← resolveBase n nt.s with
      | none => return Window.mk [] [] none
      | some w =>
        checkRange w nt.s
        return w

/-- `name AS (spec), ...` of a WINDOW clause (newest first); a base names an earlier window of the clause. -/
def windowDefs : Nat → List (String × Window) → P (List (String × Window))
  | 0, _ => synErr
  | f + 1, acc => do
    let name ← parseNm
    expect .kAS
    expect .lp
    modify fun st => { st with wins := acc }
    let (base, part, ob, fr) ← windowSpecParts f
    expect .rp
    let w ← match base with
      | none => pure (Window.mk part ob fr)
      | some (n, pos) => do
        let (w, _) ← mergeBase n pos part ob fr
        pure w
    let acc := (name, w) :: acc
    if (← curKind) == .comma then
      advance
      windowDefs f acc
    else return acc

def windowClause : Nat → P (List (String × Window))
  | 0 => synErr
  | f + 1 => do
    advance
    let st0 ← get
    modify fun st => { st with resolve := true }
    let defs ← windowDefs f []
    modify fun st => { st with wins := st0.wins, resolve := st0.resolve, named := st0.named }
    return defs

/-- Function call arguments; the current token is the '('. -/
def callArgs : Nat → String → P Expr
  | 0, _ => synErr
  | f + 1, name => do
    advance
    let k ← curKind
    let (distinct, star, args) ←
      if k == .star then
        advance
        pure (false, true, [])
      else if k == .rp then pure (false, false, [])
      else do
        let d ← accept .kDISTINCT
        if !d then
          let _ ← accept .kALL
        pure (d, false, ← parseExprList f)
    expect .rp
    let k2 ← curKind
    let isFilter := k2 == .kFILTER && (← peek1).kind == .lp
    if isFilter || isOverAt (← get) then
      let ft ← curTok
      let flt ← if isFilter then do
          advance
          advance
          expect .kWHERE
          let e ← parseExpr f
          expect .rp
          pure (some e)
        else pure none
      if !isOverAt (← get) then
        -- an aggregate's FILTER: carried as a last argument the compiler takes off (`filterTag`)
        match flt with
        | some e => return .fn name distinct star (args ++ [.fn filterTag false false [e]])
        | none => synErr
      else
        if distinct then errAt "DISTINCT is not supported for window functions" ft.s
        if flt.isSome && windowOnlyFns.contains name.toLower then
          errAt "FILTER clause may only be used with aggregate window functions" ft.s
        let w ← parseOver f
        return .window name distinct star args flt w
    else return .fn name distinct star args

def nameExpr : Nat → Token → P Expr
  | 0, _ => synErr
  | f + 1, t => do
    let st ← get
    advance
    let name := nameOf st.src t
    match ← curKind with
    | .lp => callArgs f name
    | .dot =>
      advance
      let t2 ← curTok
      if isNmKind t2.kind then
        advance
        let n2 := nameOf st.src t2
        if (← curKind) == .dot then
          advance
          let t3 ← curTok
          if isNmKind t3.kind then
            advance
            return .col (some n2) (nameOf st.src t3) false
          else synErr
        else return .col (some name) n2 false
      else synErr
    | _ =>
      match isTrueFalse st.src t with
      | some v => return .lit (.int v)
      | none => return .col none name (t.kind == .dqid)

def parsePrimary : Nat → P Expr
  | 0 => synErr
  | f + 1 => do
    let st ← get
    let t := st.tok
    match t.kind with
    | .int | .real | .hex =>
      let e ← liftE (litOfTok st.src t)
      advance
      return e
    | .str => advance; return .lit (.text (nameOf st.src t))
    | .blob => advance; return .lit (.blob (blobOf st.src (t.s + 2) (t.e - 1)))
    | .kNULL => advance; return .lit .null
    | .param => advance; return .param (sub st.src t.s t.e)
    | .lp =>
      advance
      if isSelectStart (← curKind) then
        let q ← parseSelect f
        expect .rp
        return .subquery q
      else
        let e ← parseExpr f
        if (← curKind) == .comma then
          let items ← exprRest f [e]
          expect .rp
          return .row items
        expect .rp
        return e
    | .kCASE =>
      advance
      let base ← if (← curKind) == .kWHEN then pure none else do pure (some (← parseExpr f))
      let whens ← caseWhens f []
      let els ← if (← curKind) == .kELSE then do
          advance
          pure (some (← parseExpr f))
        else pure none
      expect .kEND
      return .case base whens els
    | .kEXISTS =>
      advance
      expect .lp
      let q ← parseSelect f
      expect .rp
      return .exists q false
    | .kCAST =>
      if (← peek1).kind == .lp then
        advance
        advance
        let e ← parseExpr f
        expect .kAS
        let ty ← parseTypeName
        expect .rp
        return .cast e ty
      else nameExpr f t
    | .kCURRENT_DATE | .kCURRENT_TIME | .kCURRENT_TIMESTAMP =>
      advance
      return .fn (sub st.src t.s t.e) false false []
    | .kRAISE =>
      if (← peek1).kind == .lp then
        advance
        advance
        let rk ← curKind
        match rk with
        | .kIGNORE =>
          advance
          expect .rp
          return .raise .ignore ""
        | .kROLLBACK | .kABORT | .kFAIL =>
          advance
          expect .comma
          let mt ← curTok
          let m ← parseExpr f
          expect .rp
          let kind : RaiseKind := match rk with
            | .kROLLBACK => .rollback
            | .kABORT => .abort
            | _ => .fail
          match m with
          | .lit (.text s) => return .raise kind s
          | _ => errAt "lean-sqlite: unsupported: RAISE with a message that is not a string literal" mt.s
        | _ => synErr
      else nameExpr f t
    | k =>
      if isIdKind k || k.isJoinKw then nameExpr f t else synErr

def parseSelect : Nat → P Select
  | 0 => synErr
  | f + 1 => do
    let (recursive, ctes) ← if (← curKind) == .kWITH then parseWith f else pure (false, [])
    match ← curKind with
    | .kINSERT | .kUPDATE | .kDELETE | .kREPLACE => unsupported "WITH ... INSERT/UPDATE/DELETE"
    | _ => pure ()
    let first ← parseCore f
    let rest ← compoundRest f []
    let orderBy ← if (← curKind) == .kORDER then do
        advance
        expect .kBY
        orderTerms f []
      else pure []
    let (limit, offset) ← if (← curKind) == .kLIMIT then do
        advance
        let e1 ← parseExpr f
        match ← curKind with
        | .kOFFSET =>
          advance
          let e2 ← parseExpr f
          pure (some e1, some e2)
        | .comma =>
          advance
          let e2 ← parseExpr f
          pure (some e2, some e1)
        | _ => pure (some e1, none)
      else pure (none, none)
    return .mk recursive ctes first rest orderBy limit offset

def parseWith : Nat → P (Bool × List Cte)
  | 0 => synErr
  | f + 1 => do
    advance
    let r ← accept .kRECURSIVE
    let ctes ← cteList f []
    return (r, ctes)

def cteList : Nat → List Cte → P (List Cte)
  | 0, _ => synErr
  | f + 1, acc => do
    let name ← parseNm
    let cols ← if (← curKind) == .lp then do
        advance
        let ns ← nmList
        expect .rp
        pure ns
      else pure []
    expect .kAS
    if (← curKind) == .kNOT then
      advance
      expect .kMATERIALIZED
    else if (← curKind) == .kMATERIALIZED then advance
    expect .lp
    let q ← parseSelect f
    expect .rp
    let acc := Cte.mk name cols q :: acc
    if (← curKind) == .comma then
      advance
      cteList f acc
    else return acc.reverse

def compoundRest : Nat → List (CompoundOp × Core) → P (List (CompoundOp × Core))
  | 0, _ => synErr
  | f + 1, acc => do
    let op ← match ← curKind with
      | .kUNION => do
        advance
        let all ← accept .kALL
        pure (some (if all then CompoundOp.unionAll else CompoundOp.union))
      | .kINTERSECT => do advance; pure (some CompoundOp.intersect)
      | .kEXCEPT => do advance; pure (some CompoundOp.except)
      | _ => pure none
    match op with
    | none => return acc.reverse
    | some op =>
      let c ← parseCore f
      compoundRest f ((op, c) :: acc)

def valuesRows : Nat → List (List Expr) → P (List (List Expr))
  | 0, _ => synErr
  | f + 1, acc => do
    expect .lp
    let items ← parseExprList f
    expect .rp
    if (← curKind) == .comma then
      advance
      valuesRows f (items :: acc)
    else return (items :: acc).reverse

def selectBody : Nat → P (Core × List (String × Window))
  | 0 => synErr
  | f + 1 => do
    advance
    let distinct ← match ← curKind with
      | .kDISTINCT => do advance; pure true
      | .kALL => do advance; pure false
      | _ => pure false
    let cols ← resultCols f []
    let (frm, joins) ← if (← curKind) == .kFROM then do
        advance
        let item ← fromItem f
        match ← curKind with
        | .kON =>
          let ot ← curTok
          advance
          let _ ← parseExpr f
          deferErr "a JOIN clause is required before ON" ot.s
        | .kUSING =>
          let ot ← curTok
          advance
          expect .lp
          let _ ← nmList
          expect .rp
          deferErr "a JOIN clause is required before USING" ot.s
        | _ => pure ()
        let js ← joinLoop f []
        pure (some item, js)
      else pure (none, [])
    let whr ← if (← curKind) == .kWHERE then do
        advance
        pure (some (← parseExpr f))
      else pure none
    let groupBy ← if (← curKind) == .kGROUP then do
        advance
        expect .kBY
        parseExprList f
      else pure []
    let having ← if (← curKind) == .kHAVING then do
        advance
        pure (some (← parseExpr f))
      else pure none
    let defs ← if isWindowClauseAt (← get) then windowClause f else pure []
    return (.select distinct cols frm joins whr groupBy having, defs)

/-- A SELECT core or VALUES. A core that names a window is parsed twice: the first time finds its WINDOW clause (it comes after
the calls that use it), the second resolves the names against it. -/
def parseCore : Nat → P Core
  | 0 => synErr
  | f + 1 => do
    match ← curKind with
    | .kSELECT =>
      let st0 ← get
      set { st0 with wins := [], resolve := false, named := false }
      let (core, defs) ← selectBody f
      let st1 ← get
      let (core, st1) ← if st1.named then do
          set { st0 with wins := defs, resolve := true, named := false, late := st1.late }
          let (c2, _) ← selectBody f
          pure (c2, ← get)
        else pure (core, st1)
      set { st1 with wins := st0.wins, resolve := st0.resolve, named := st0.named }
      return core
    | .kVALUES =>
      advance
      return .values (← valuesRows f [])
    | _ => synErr

def resultCols : Nat → List ResultCol → P (List ResultCol)
  | 0, _ => synErr
  | f + 1, acc => do
    let st ← get
    let t := st.tok
    let col ←
      if t.kind == .star then do
        advance
        pure ResultCol.star
      else do
        let isT := isIdKind t.kind &&
          (let n1 := lexTok st.src t.e
           n1.kind == .dot && (lexTok st.src n1.e).kind == .star)
        if isT then
          advance
          advance
          advance
          pure (ResultCol.tableStar (nameOf st.src t))
        else
          let e ← parseExpr f
          let st2 ← get
          let alias ← parseAlias
          pure (ResultCol.expr e alias (sub st.src t.s st2.prevEnd))
    if (← curKind) == .comma then
      advance
      resultCols f (col :: acc)
    else return (col :: acc).reverse

def fromItem : Nat → P FromItem
  | 0 => synErr
  | f + 1 => do
    let st ← get
    let k := st.tok.kind
    if k == .lp then
      advance
      if isSelectStart (← curKind) then
        let q ← parseSelect f
        expect .rp
        return .subquery q (← parseAlias)
      else unsupported "parenthesized join"
    else if isNmKind k then
      let (name, _) ← parseQNameM
      let k2 ← curKind
      if k2 == .lp then
        -- a table-valued function: name(args)
        advance
        let args ← if (← curKind) == .rp then pure [] else parseExprList f
        expect .rp
        return .call (Schema'.bare name) args (← parseAlias)
      else
        let alias ← parseAlias
        -- INDEXED BY name / NOT INDEXED: an access-path hint; the results are the same without it
        let k3 ← curKind
        if k3 == .kINDEXED && (← peek1).kind == .kBY then
          advance; advance
          let _ ← parseNm
        else if k3 == .kNOT && (← peek1).kind == .kINDEXED then
          advance; advance
        return .table name alias
    else synErr

def joinLoop : Nat → List Join → P (List Join)
  | 0, _ => synErr
  | f + 1, acc => do
    let k ← curKind
    let jk? : Option (JoinKind × Bool) ←
      match k with
      | .comma => do advance; pure (some (.cross, false))
      | .kJOIN => do advance; pure (some (.inner, false))
      | _ => if k.isJoinKw then do pure (some (← joinOp)) else pure none
    match jk? with
    | none => return acc.reverse
    | some (jk, natural) =>
      let item ← fromItem f
      let ct ← curTok
      let (on, usingCols) ←
        match ← curKind with
        | .kON => do
          advance
          pure (some (← parseExpr f), [])
        | .kUSING => do
          advance
          expect .lp
          let ns ← nmList
          expect .rp
          pure (none, ns)
        | _ => pure (none, [])
      if natural && (on.isSome || !usingCols.isEmpty) then errAt "a NATURAL join may not have an ON or USING clause" ct.s
      joinLoop f (Join.mk jk item on (if natural then ["*"] else usingCols) :: acc)

def orderTerms : Nat → List OrderTerm → P (List OrderTerm)
  | 0, _ => synErr
  | f + 1, acc => do
    let e ← parseExpr f
    let desc ← match ← curKind with
      | .kASC => do advance; pure false
      | .kDESC => do advance; pure true
      | _ => pure false
    let nulls ← if (← curKind) == .kNULLS then do
        advance
        match ← curKind with
        | .kFIRST => do advance; pure (some true)
        | .kLAST => do advance; pure (some false)
        | _ => synErr
      else pure none
    let acc := OrderTerm.mk e desc nulls :: acc
    if (← curKind) == .comma then
      advance
      orderTerms f acc
    else return acc.reverse

end

def ex : P Expr := do parseExpr (← fuelOf) 
def sel : P Select := do parseSelect (← fuelOf)

/-! ## Statements -/

/-- ON CONFLICT algorithm of a constraint (parsed, then dropped: the AST does not carry it). -/
def parseConflictAlgo : P Conflict := do
  match ← curKind with
  | .kROLLBACK => advance; return .rollback
  | .kABORT => advance; return .abort
  | .kFAIL => advance; return .fail
  | .kIGNORE => advance; return .ignore
  | .kREPLACE => advance; return .replace
  | _ => synErr

def parseConflict : P Unit := do
  if (← curKind) == .kON && (← peek1).kind == .kCONFLICT then
    advance
    advance
    let _ ← parseConflictAlgo

/-- [INITIALLY DEFERRED|IMMEDIATE] after DEFERRABLE. -/
def deferrable : P Unit := do
  if (← curKind) == .kINITIALLY then
    advance
    match ← curKind with
    | .kDEFERRED | .kIMMEDIATE => advance
    | _ => synErr

def skipRefArgs : Nat → P Unit
  | 0 => pure ()
  | f + 1 => do
    match ← curKind with
    | .kON =>
      advance
      match ← curKind with
      | .kDELETE | .kUPDATE | .kINSERT => advance
      | _ => synErr
      match ← curKind with
      | .kSET =>
        advance
        match ← curKind with
        | .kNULL | .kDEFAULT => advance
        | _ => synErr
      | .kCASCADE | .kRESTRICT => advance
      | .kNO => advance; expect .kACTION
      | _ => synErr
      skipRefArgs f
    | .kMATCH =>
      advance
      let _ ← parseNm
      skipRefArgs f
    | .kNOT =>
      if (← peek1).kind == .kDEFERRABLE then
        advance
        advance
        deferrable
        skipRefArgs f
    | .kDEFERRABLE =>
      advance
      deferrable
      skipRefArgs f
    | _ => pure ()

/-- After REFERENCES: table [(cols)] and the ON/MATCH/DEFERRABLE clauses, all ignored. -/
def skipReferences : P Unit := do
  let _ ← parseNm
  if (← curKind) == .lp then
    advance
    let _ ← nmList
    expect .rp
  skipRefArgs (← fuelOf)

def parseDefault : P Expr := do
  let st ← get
  let t := st.tok
  match t.kind with
  | .lp =>
    advance
    let e ← ex
    expect .rp
    return e
  | .minus | .plus =>
    advance
    let t2 ← curTok
    let neg := t.kind == .minus
    match t2.kind with
    | .int | .real | .hex | .str | .blob | .kNULL | .kCURRENT_DATE | .kCURRENT_TIME | .kCURRENT_TIMESTAMP =>
      if neg && isMinMag st.src t2 then
        advance
        return .lit int64Min
      else
        let e ← parsePrimary (← fuelOf)
        return (if neg then .un .neg e else e)
    | _ => synErr
  | .int | .real | .hex | .str | .blob | .kNULL | .kCURRENT_DATE | .kCURRENT_TIME | .kCURRENT_TIMESTAMP =>
    parsePrimary (← fuelOf)
  | k =>
    if isIdKind k then
      advance
      match isTrueFalse st.src t with
      | some v => return .lit (.int v)
      | none => return .lit (.text (nameOf st.src t))
    else synErr

def colCons (cd : ColumnDef) : Nat → P ColumnDef
  | 0 => return cd
  | f + 1 => do
    match ← curKind with
    | .kCONSTRAINT =>
      advance
      let _ ← parseNm
      colCons cd f
    | .kPRIMARY =>
      advance
      expect .kKEY
      let d ← match ← curKind with
        | .kASC => do advance; pure false
        | .kDESC => do advance; pure true
        | _ => pure false
      parseConflict
      let ai ← accept .kAUTOINCREMENT
      colCons { cd with primaryKey := true, pkDesc := d, autoincrement := ai } f
    | .kNOT =>
      if (← peek1).kind == .kDEFERRABLE then
        advance
        advance
        deferrable
        colCons cd f
      else
        advance
        expect .kNULL
        parseConflict
        colCons { cd with notNull := true } f
    | .kDEFERRABLE =>
      advance
      deferrable
      colCons cd f
    | .kNULL =>
      advance
      parseConflict
      colCons cd f
    | .kUNIQUE =>
      advance
      parseConflict
      colCons { cd with unique := true } f
    | .kCHECK =>
      advance
      expect .lp
      let e ← ex
      expect .rp
      colCons { cd with check := cd.check ++ [e] } f
    | .kDEFAULT =>
      advance
      let d ← parseDefault
      colCons { cd with default := some d } f
    | .kCOLLATE =>
      advance
      let n ← parseNm
      colCons { cd with collate := some n } f
    | .kREFERENCES =>
      advance
      skipReferences
      colCons cd f
    | .kGENERATED | .kAS => unsupported "generated columns"
    | _ => return cd

def parseColumnDef : P ColumnDef := do
  let name ← parseNm
  let type ← parseTypeName
  colCons { name, type } (← fuelOf)

def isPlainIdxEnd (k : TK) : Bool :=
  k == .comma || k == .rp || k == .kCOLLATE || k == .kASC || k == .kDESC || k == .kAUTOINCREMENT

/-- One entry of an index column list (a PRIMARY KEY / UNIQUE constraint, CREATE INDEX, an upsert target), then more after commas;
the flag: AUTOINCREMENT was seen. A term that is not a plain column name is an expression (`allowExpr`) with `name` its source text. -/
def indexedColsAux (allowExpr : Bool) : Nat → List IndexedCol → Bool → P (List IndexedCol × Bool)
  | 0, _, _ => synErr
  | f + 1, acc, ai => do
    let st ← get
    let t := st.tok
    let k0 := t.kind
    if k0 == .rp || k0 == .comma || k0 == .semi || k0 == .eof then synErr
    let mut name := ""
    let mut collate : Option String := none
    let mut ex? : Option Expr := none
    if isNmKind k0 && isPlainIdxEnd (lexTok st.src t.e).kind then
      name ← parseNm
      if (← curKind) == .kCOLLATE then
        advance
        collate := some (← parseNm)
    else
      let e ← parseExpr f
      let pe := (← get).prevEnd
      if !allowExpr then
        deferErr "expressions prohibited in PRIMARY KEY and UNIQUE constraints" t.s
      name := sub st.src t.s pe
      match e with
      | .collate inner c =>
        collate := some c
        ex? := some inner
      | _ => ex? := some e
    let desc ← match ← curKind with
      | .kASC => do advance; pure false
      | .kDESC => do advance; pure true
      | _ => pure false
    let ai2 ← accept .kAUTOINCREMENT
    let k ← curKind
    if k != .comma && k != .rp then synErr
    let acc := ({ name, collate, desc, expr := ex? } : IndexedCol) :: acc
    if k == .comma then
      advance
      indexedColsAux allowExpr f acc (ai || ai2)
    else return (acc.reverse, ai || ai2)

def indexedCols (allowExpr : Bool := false) : P (List IndexedCol × Bool) := do indexedColsAux allowExpr (← fuelOf) [] false

def parseTableConstraint : P TableConstraint := do
  if (← curKind) == .kCONSTRAINT then
    advance
    let _ ← parseNm
  match ← curKind with
  | .kPRIMARY =>
    advance
    expect .kKEY
    expect .lp
    let (cols, ai) ← indexedCols
    expect .rp
    parseConflict
    return .primaryKey cols ai
  | .kUNIQUE =>
    advance
    expect .lp
    let (cols, _) ← indexedCols
    expect .rp
    parseConflict
    return .unique cols
  | .kCHECK =>
    advance
    expect .lp
    let e ← ex
    expect .rp
    return .check e
  | .kFOREIGN =>
    advance
    expect .kKEY
    expect .lp
    let _ ← nmList
    expect .rp
    expect .kREFERENCES
    skipReferences
    return .foreignKey
  | _ => synErr

def parseIfNotExists : P Bool := do
  if (← curKind) == .kIF then
    advance
    expect .kNOT
    expect .kEXISTS
    return true
  else return false

def parseIfExists : P Bool := do
  if (← curKind) == .kIF then
    advance
    expect .kEXISTS
    return true
  else return false

def isSpaceLike (c : UInt8) : Bool := isSpace c || c == 11

/-- The end offset of bytes [s, e) without trailing whitespace. -/
def trimEnd (src : String) (s : Nat) : Nat → Nat
  | 0 => s
  | f + 1 => if f >= 0 && s < f + 1 && isSpaceLike (byteAt src f) then trimEnd src s f else f + 1

def consStart (k : TK) : Bool := k == .kCONSTRAINT || k == .kPRIMARY || k == .kUNIQUE || k == .kCHECK || k == .kFOREIGN

def parseCreateTable (isTemp : Bool) : P Stmt := do
  let ine ← parseIfNotExists
  let (name, nameStart) ← parseCreateName isTemp "temporary table name must be unqualified"
  if (← curKind) == .kAS then
    advance
    let q ← sel
    return .createTableAs name ine q
  expect .lp
  let n ← fuelOf
  let mut cols : Array ColumnDef := #[]
  let mut cons : Array TableConstraint := #[]
  for _ in [0:n] do
    if consStart (← curKind) then
      cons := cons.push (← parseTableConstraint)
    else if cons.isEmpty then
      cols := cols.push (← parseColumnDef)
    else synErr
    if (← curKind) == .comma then advance else break
  if cols.isEmpty then synErr
  let rpEnd := (← curTok).e
  expect .rp
  let mut without := false
  let mut hasOpts := false
  let mut strict := false
  for _ in [0:n] do
    let st ← get
    let k := st.tok.kind
    if k == .kWITHOUT then
      advance
      let t ← curTok
      if t.kind == .id && t.e - t.s == 5 && eqFold "ROWID" st.src t.s 5 then advance else synErr
      without := true
    else if k == .id && st.tok.e - st.tok.s == 6 && eqFold "STRICT" st.src st.tok.s 6 then advance; strict := true
    else if hasOpts then synErr
    else break
    hasOpts := true
    if (← curKind) == .comma then advance else break
  let st ← get
  let endPos := if hasOpts then st.tok.s else rpEnd
  return .createTable name ine cols.toList (cons.toList ++ (if strict then [TableConstraint.strict] else [])) without
    ("CREATE TABLE " ++ sub st.src nameStart endPos)

def parseCreateIndex (unique : Bool) : P Stmt := do
  let ine ← parseIfNotExists
  let (name, nameStart) ← parseQName
  expect .kON
  let table ← parseNm
  expect .lp
  let (cols, _) ← indexedCols true
  expect .rp
  let whr ← if (← curKind) == .kWHERE then do
      advance
      pure (some (← ex))
    else pure none
  let st ← get
  let pre := if unique then "CREATE UNIQUE INDEX " else "CREATE INDEX "
  return .createIndex name table cols unique ine whr (pre ++ sub st.src nameStart st.tok.s)

def parseCreateView (isTemp : Bool) : P Stmt := do
  let ine ← parseIfNotExists
  let (name, nameStart) ← parseCreateName isTemp "temporary table name must be unqualified"
  let cols ← if (← curKind) == .lp then do
      advance
      let ns ← nmList
      expect .rp
      pure ns
    else pure []
  expect .kAS
  let q ← sel
  let st ← get
  let e := trimEnd st.src nameStart st.tok.s
  return .createView name ine cols q ("CREATE VIEW " ++ sub st.src nameStart e)

def parseDrop : P Stmt := do
  advance
  let k ← curKind
  match k with
  | .kTABLE | .kINDEX | .kVIEW =>
    advance
    let ie ← parseIfExists
    let (name, _) ← parseQNameM
    return match k with
      | .kTABLE => .dropTable name ie
      | .kINDEX => .dropIndex name ie
      | _ => .dropView name ie
  | .kTRIGGER =>
    advance
    let ie ← parseIfExists
    let (name, _) ← parseQNameM
    return .dropTrigger name ie
  | _ => synErr

def parseOnConflictOpt : P Conflict := do
  if (← curKind) == .kOR then
    advance
    parseConflictAlgo
  else return .abort

/-- After INSERT/UPDATE/DELETE: an optional RETURNING list (not allowed in a trigger body). -/
def returningTail (trig : Bool) (s : Stmt) : P Stmt := do
  let t ← curTok
  if t.kind == .kRETURNING then
    advance
    if trig then deferErr "cannot use RETURNING in a trigger" t.s
    return .returning s (← resultCols (← fuelOf) [])
  else return s

/-- `col = e, (c1, c2) = (e1, e2), ...` of UPDATE and DO UPDATE. -/
def parseSetList : P (List (String × Expr)) := do
  let n ← fuelOf
  let mut sets : Array (String × Expr) := #[]
  for _ in [0:n] do
    if (← curKind) == .lp then
      -- (a, b) = (x, y)
      advance
      let cols ← nmList
      expect .rp
      expect .eq
      expect .lp
      if isSelectStart (← curKind) then unsupported "SET (columns) = (SELECT ...)"
      let mut es : Array Expr := #[]
      for _ in [0:cols.length] do
        es := es.push (← ex)
        if (← curKind) == .comma then advance else break
      expect .rp
      if es.size != cols.length then unsupported "row value misused"
      sets := sets ++ (cols.toArray.zip es)
    else
      let col ← parseNm
      expect .eq
      sets := sets.push (col, ← ex)
    if (← curKind) == .comma then advance else break
  return sets.toList

def parseUpdate (trig : Bool) : P Stmt := do
  advance
  let c ← parseOnConflictOpt
  let (name, _) ← parseQNameM
  let alias ← if (← curKind) == .kAS then do advance; pure (some (← parseNm)) else pure none
  expect .kSET
  let sets ← parseSetList
  if (← curKind) == .kFROM then unsupported "UPDATE FROM"
  let whr ← if (← curKind) == .kWHERE then do
      advance
      pure (some (← ex))
    else pure none
  match ← curKind with
  | .kORDER | .kLIMIT => unsupported "UPDATE ... ORDER BY / LIMIT"
  | _ => pure ()
  returningTail trig (.update c name alias sets whr)

/-- After DO: NOTHING, or UPDATE SET .. [WHERE ..]. -/
def upsertAction : P (Option (List (String × Expr) × Option Expr)) := do
  match ← curKind with
  | .kNOTHING =>
    advance
    return none
  | .kUPDATE =>
    advance
    expect .kSET
    let sets ← parseSetList
    let w ← if (← curKind) == .kWHERE then do
        advance
        pure (some (← ex))
      else pure none
    return some (sets, w)
  | _ => synErr

/-- The ON CONFLICT clauses after an INSERT's source: those with a conflict target may repeat, one without ends the list. -/
def upsertClauses : Nat → List Upsert → P (List Upsert)
  | 0, _ => synErr
  | f + 1, acc => do
    if (← curKind) == .kON && (← peek1).kind == .kCONFLICT then
      advance
      advance
      if (← curKind) == .lp then
        advance
        let (cols, _) ← indexedCols true
        expect .rp
        let tw ← if (← curKind) == .kWHERE then do
            advance
            pure (some (← ex))
          else pure none
        expect .kDO
        let u ← upsertAction
        upsertClauses f ({ target := cols, targetWhere := tw, update := u } :: acc)
      else
        expect .kDO
        let u ← upsertAction
        return ({ update := u } :: acc).reverse
    else return acc.reverse

def parseInsertBody (c : Conflict) : P Stmt := do
  expect .kINTO
  let (name, _) ← parseQNameM
  if (← curKind) == .kAS then
    advance
    let _ ← parseNm
  let cols ← if (← curKind) == .lp then do
      advance
      let ns ← nmList
      expect .rp
      pure ns
    else pure []
  let src ← match ← curKind with
    | .kVALUES => do
      advance
      pure (InsertSource.values (← valuesRows (← fuelOf) []))
    | .kSELECT | .kWITH => do pure (InsertSource.select (← sel))
    | .kDEFAULT => do
      advance
      expect .kVALUES
      pure InsertSource.defaults
    | _ => synErr
  let ups ← match src with
    | .defaults => pure []
    | _ => upsertClauses (← fuelOf) []
  return .insert c name cols src ups

def parseInsert (trig : Bool) (c : Conflict) : P Stmt := do
  returningTail trig (← parseInsertBody c)

def parseDelete (trig : Bool) : P Stmt := do
  advance
  expect .kFROM
  let (name, _) ← parseQNameM
  let alias ← if (← curKind) == .kAS then do advance; pure (some (← parseNm)) else pure none
  let whr ← if (← curKind) == .kWHERE then do
      advance
      pure (some (← ex))
    else pure none
  match ← curKind with
  | .kORDER | .kLIMIT => unsupported "DELETE ... ORDER BY / LIMIT"
  | _ => pure ()
  returningTail trig (.delete name alias whr)

def parsePragmaValue : P String := do
  let st ← get
  let t := st.tok
  match t.kind with
  | .plus | .minus =>
    advance
    let t2 ← curTok
    if t2.kind == .int || t2.kind == .real || t2.kind == .hex then
      advance
      return (if t.kind == .minus then "-" else "") ++ sub st.src t2.s t2.e
    else synErr
  | .int | .real | .hex | .kON | .kDELETE | .kDEFAULT =>
    advance
    return sub st.src t.s t.e
  | _ => parseNm

def parsePragma : P Stmt := do
  advance
  let (name, _) ← parseQName
  match ← curKind with
  | .eq =>
    advance
    return .pragma name (some (← parsePragmaValue))
  | .lp =>
    advance
    let v ← parsePragmaValue
    expect .rp
    return .pragma name (some v)
  | _ => return .pragma name none

def parseAlter : P Stmt := do
  advance
  expect .kTABLE
  let (name, _) ← parseQNameM
  match ← curKind with
  | .kRENAME =>
    advance
    if (← curKind) == .kTO then
      advance
      return .alterRename name (← parseNm)
    else
      let _ ← accept .kCOLUMN
      let old ← parseNm
      expect .kTO
      return .alterRenameColumn name old (← parseNm)
  | .kADD =>
    advance
    let _ ← accept .kCOLUMN
    let start := (← curTok).s
    let col ← parseColumnDef
    let st ← get
    return .alterAddColumn name col (sub st.src start (trimEnd st.src start st.tok.s))
  | .kDROP =>
    advance
    let _ ← accept .kCOLUMN
    return .alterDropColumn name (← parseNm)
  | _ => synErr

/-- [TRANSACTION [name]] -/
def transOpt : P Unit := do
  if (← curKind) == .kTRANSACTION then
    advance
    if isNmKind (← curKind) then
      let _ ← parseNm

/-- The WITH tables of a statement given to its query: a SELECT's own, or an INSERT's source. -/
def withCtes (recursive : Bool) (ctes : List Cte) : Select → Select
  | .mk r cs first rest ob lim off => .mk (r || recursive) (ctes ++ cs) first rest ob lim off

/-- `e` with `WITH ctes` put on each outermost subquery in it (where UPDATE and DELETE can name a CTE). -/
def withExpr (recursive : Bool) (ctes : List Cte) : Nat → Expr → Expr
  | 0, e => e
  | f+1, e =>
    let w := withExpr recursive ctes f
    match e with
    | .lit _ | .col .. | .param _ | .raise .. | .window .. => e
    | .bin op a b => .bin op (w a) (w b)
    | .un op a => .un op (w a)
    | .fn n d s args => .fn n d s (args.map w)
    | .cast a t => .cast (w a) t
    | .collate a c => .collate (w a) c
    | .case b ws el => .case (b.map w) (ws.map fun (x, y) => (w x, w y)) (el.map w)
    | .between a lo hi n => .between (w a) (w lo) (w hi) n
    | .inList a items n => .inList (w a) (items.map w) n
    | .inSelect a q n => .inSelect (w a) (withCtes recursive ctes q) n
    | .matches op a p esc n => .matches op (w a) (w p) (esc.map w) n
    | .isNull a n => .isNull (w a) n
    | .exists q n => .exists (withCtes recursive ctes q) n
    | .subquery q => .subquery (withCtes recursive ctes q)
    | .row items => .row (items.map w)

/-- An UPDATE or DELETE under `WITH ctes`. -/
def withStmt (recursive : Bool) (ctes : List Cte) : Stmt → Stmt
  | .update c t a sets whr => .update c t a (sets.map fun (n, e) => (n, withExpr recursive ctes 1000 e))
      (whr.map (withExpr recursive ctes 1000))
  | .delete t a whr => .delete t a (whr.map (withExpr recursive ctes 1000))
  | .returning (.update c t a sets whr) cols => .returning (withStmt recursive ctes (.update c t a sets whr)) cols
  | .returning (.delete t a whr) cols => .returning (withStmt recursive ctes (.delete t a whr)) cols
  | s => s

/-- INSERT, UPDATE, DELETE, SELECT, VALUES, and WITH in front of one of them. -/
def parseDml (trig : Bool := false) : P Stmt := do
  match ← curKind with
  | .kWITH => do
    let (recursive, ctes) ← parseWith (← fuelOf)
    match ← curKind with
    | .kINSERT | .kREPLACE => do
      let c ← if (← curKind) == .kREPLACE then do advance; pure Conflict.replace else do advance; parseOnConflictOpt
      match ← parseInsertBody c with
      | .insert c t cols (.select q) ups => returningTail trig (.insert c t cols (.select (withCtes recursive ctes q)) ups)
      | .insert c t cols (.values rows) ups =>
        returningTail trig (.insert c t cols (.select (.mk recursive ctes (.values rows) [] [] none none)) ups)
      | s => returningTail trig s
    | .kUPDATE => return withStmt recursive ctes (← parseUpdate trig)
    | .kDELETE => return withStmt recursive ctes (← parseDelete trig)
    | _ => return .select (withCtes recursive ctes (← sel))
  | .kSELECT | .kVALUES => return .select (← sel)
  | .kINSERT =>
    advance
    parseInsert trig (← parseOnConflictOpt)
  | .kREPLACE =>
    advance
    parseInsert trig .replace
  | .kUPDATE => parseUpdate trig
  | .kDELETE => parseDelete trig
  | _ => synErr

/-- After CREATE [TEMP] TRIGGER. -/
def parseCreateTrigger (isTemp : Bool) : P Stmt := do
  let ine ← parseIfNotExists
  let (name, nameStart) ← parseCreateName isTemp "temporary trigger may not have qualified name"
  let timing ← match ← curKind with
    | .kBEFORE => do advance; pure TriggerTiming.before
    | .kAFTER => do advance; pure TriggerTiming.after
    | .kINSTEAD => do advance; expect .kOF; pure TriggerTiming.insteadOf
    | _ => pure TriggerTiming.before
  let event ← match ← curKind with
    | .kDELETE => do advance; pure TriggerEvent.delete
    | .kINSERT => do advance; pure TriggerEvent.insert
    | .kUPDATE => do
      advance
      if (← curKind) == .kOF then
        advance
        pure (TriggerEvent.update (← nmList))
      else pure (TriggerEvent.update [])
    | _ => synErr
  expect .kON
  let (table, _) ← parseQName
  if (← curKind) == .kFOR then
    advance
    expect .kEACH
    expect .kROW
  let whn ← if (← curKind) == .kWHEN then do
      advance
      pure (some (← ex))
    else pure none
  expect .kBEGIN
  let n ← fuelOf
  let mut body : Array Stmt := #[]
  for _ in [0:n] do
    body := body.push (← parseDml true)
    expect .semi
    if (← curKind) == .kEND then break
  expect .kEND
  let st ← get
  return .createTrigger name ine timing event table whn body.toList ("CREATE TRIGGER " ++ sub st.src nameStart st.prevEnd)

def parseCreate : P Stmt := do
  advance
  let mut k ← curKind
  let isTemp := k == .kTEMP
  if isTemp then
    advance
    k ← curKind
  modify fun s => { s with tmpName := false }
  let wrap (r : Stmt) : P Stmt := do
    if isTemp || (← get).tmpName then return .temp r else return r
  match k with
  | .kTABLE => advance; wrap (← parseCreateTable isTemp)
  | .kVIEW => advance; wrap (← parseCreateView isTemp)
  | .kINDEX => if isTemp then synErr else do advance; parseCreateIndex false
  | .kUNIQUE =>
    if isTemp then synErr
    advance
    expect .kINDEX
    parseCreateIndex true
  | .kVIRTUAL => unsupported "CREATE VIRTUAL TABLE"
  | .kTRIGGER => advance; wrap (← parseCreateTrigger isTemp)
  | _ => synErr

def parseStmt : P Stmt := do
  match ← curKind with
  | .kWITH | .kSELECT | .kVALUES | .kINSERT | .kREPLACE | .kUPDATE | .kDELETE => parseDml
  | .kCREATE => parseCreate
  | .kDROP => parseDrop
  | .kBEGIN =>
    advance
    match ← curKind with
    | .kDEFERRED | .kIMMEDIATE | .kEXCLUSIVE => advance
    | _ => pure ()
    transOpt
    return .begin
  | .kCOMMIT | .kEND =>
    advance
    transOpt
    return .commit
  | .kROLLBACK =>
    advance
    transOpt
    if (← curKind) == .kTO then
      advance
      let _ ← accept .kSAVEPOINT
      return .rollbackTo (← parseNm)
    return .rollback
  | .kPRAGMA => parsePragma
  | .kALTER => parseAlter
  | .kVACUUM =>
    advance
    if isNmKind (← curKind) then
      let _ ← parseNm
    if (← curKind) == .kINTO then unsupported "VACUUM INTO"
    return .vacuum
  | .kEXPLAIN => unsupported "EXPLAIN"
  | .kATTACH => unsupported "ATTACH"
  | .kDETACH => unsupported "DETACH"
  | .kSAVEPOINT =>
    advance
    return .savepoint (← parseNm)
  | .kRELEASE =>
    advance
    let _ ← accept .kSAVEPOINT
    return .release (← parseNm)
  | .kANALYZE => unsupported "ANALYZE"
  | .kREINDEX =>
    advance
    if isNmKind (← curKind) then
      let _ ← parseQName
    return .reindex
  | _ => synErr

/-- First token that is not a ';' at or after pos. -/
def skipSemis (src : String) (pos : Nat) : Nat → Token
  | 0 => lexTok src pos
  | f + 1 =>
    let t := lexTok src pos
    if t.kind == .semi then skipSemis src t.e f else t

/-- Parses the first statement of `src` from byte offset `pos`: skips whitespace, comments and empty statements (`;`); `none` when
nothing else is left. On success: the statement and the byte offset just after its terminating `;` (or the end of input). -/
def parseNext (src : String) (pos : Nat) : Except ParseError (Option (Stmt × Nat)) :=
  let t := skipSemis src pos (src.utf8ByteSize + 1)
  if t.kind == .eof then .ok none
  else if t.kind == .illegal then .error ⟨s!"unrecognized token: \"{sub src t.s t.e}\"", t.s⟩
  else
    let r : Except ParseError ((Stmt × Nat) × PS) := (do
      let s ← parseStmt
      let tk ← curTok
      match tk.kind with
      | .semi | .eof =>
        match (← get).late with
        | some e => liftE (.error e)
        | none => pure (s, tk.e)
      | _ => synErr).run { src, tok := t, prevEnd := pos }
    match r with
    | .ok (v, _) => .ok (some v)
    | .error e => .error e

/-- The shell's line_is_complete: true when the text's last token (ignoring whitespace and comments) is `;`. -/
def isComplete (src : String) : Bool := LSql.Lex.isComplete src

end LSql.Parse
