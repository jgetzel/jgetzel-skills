import Init
/-! The SQL tokenizer (sqlite's tokenize.c): works on the bytes of a `String` (`getUtf8Byte`), allocates nothing per token. -/
namespace LSql.Lex

/-- Token kinds. Keywords are the `k*` constructors (sqlite's keyword table, mkkeywordhash.c). -/
inductive TK where
  | eof | illegal
  | id | qid | dqid | str | blob | int | real | hex | param
  | semi | comma | lp | rp | dot | star | slash | rem | plus | minus | concat
  | bitand | bitor | shl | shr | lt | le | gt | ge | eq | ne | bitnot | ptr | ptr2
  | kABORT
  | kACTION
  | kADD
  | kAFTER
  | kALL
  | kALTER
  | kALWAYS
  | kANALYZE
  | kAND
  | kAS
  | kASC
  | kATTACH
  | kAUTOINCREMENT
  | kBEFORE
  | kBEGIN
  | kBETWEEN
  | kBY
  | kCASCADE
  | kCASE
  | kCAST
  | kCHECK
  | kCOLLATE
  | kCOLUMN
  | kCOMMIT
  | kCONFLICT
  | kCONSTRAINT
  | kCREATE
  | kCROSS
  | kCURRENT
  | kCURRENT_DATE
  | kCURRENT_TIME
  | kCURRENT_TIMESTAMP
  | kDATABASE
  | kDEFAULT
  | kDEFERRED
  | kDEFERRABLE
  | kDELETE
  | kDESC
  | kDETACH
  | kDISTINCT
  | kDO
  | kDROP
  | kEND
  | kEACH
  | kELSE
  | kESCAPE
  | kEXCEPT
  | kEXCLUSIVE
  | kEXCLUDE
  | kEXISTS
  | kEXPLAIN
  | kFAIL
  | kFILTER
  | kFIRST
  | kFOLLOWING
  | kFOR
  | kFOREIGN
  | kFROM
  | kFULL
  | kGENERATED
  | kGLOB
  | kGROUP
  | kGROUPS
  | kHAVING
  | kIF
  | kIGNORE
  | kIMMEDIATE
  | kIN
  | kINDEX
  | kINDEXED
  | kINITIALLY
  | kINNER
  | kINSERT
  | kINSTEAD
  | kINTERSECT
  | kINTO
  | kIS
  | kISNULL
  | kJOIN
  | kKEY
  | kLAST
  | kLEFT
  | kLIKE
  | kLIMIT
  | kMATCH
  | kMATERIALIZED
  | kNATURAL
  | kNO
  | kNOT
  | kNOTHING
  | kNOTNULL
  | kNULL
  | kNULLS
  | kOF
  | kOFFSET
  | kON
  | kOR
  | kORDER
  | kOTHERS
  | kOUTER
  | kOVER
  | kPARTITION
  | kPLAN
  | kPRAGMA
  | kPRECEDING
  | kPRIMARY
  | kQUERY
  | kRAISE
  | kRANGE
  | kRECURSIVE
  | kREFERENCES
  | kREGEXP
  | kREINDEX
  | kRELEASE
  | kRENAME
  | kREPLACE
  | kRESTRICT
  | kRETURNING
  | kRIGHT
  | kROLLBACK
  | kROW
  | kROWS
  | kSAVEPOINT
  | kSELECT
  | kSET
  | kTABLE
  | kTEMP
  | kTHEN
  | kTIES
  | kTO
  | kTRANSACTION
  | kTRIGGER
  | kUNBOUNDED
  | kUNION
  | kUNIQUE
  | kUPDATE
  | kUSING
  | kVACUUM
  | kVALUES
  | kVIEW
  | kVIRTUAL
  | kWHEN
  | kWHERE
  | kWINDOW
  | kWITH
  | kWITHOUT
  deriving DecidableEq, Repr, Inhabited, BEq

/-- Keywords that parse.y's `%fallback ID` lets stand for an identifier (and INDEXED, which is in the `id` token class). -/
def TK.isFallback : TK → Bool
  | .kABORT
  | .kACTION
  | .kAFTER
  | .kANALYZE
  | .kASC
  | .kATTACH
  | .kBEFORE
  | .kBEGIN
  | .kBY
  | .kCASCADE
  | .kCAST
  | .kCOLUMN
  | .kCONFLICT
  | .kDATABASE
  | .kDEFERRED
  | .kDESC
  | .kDETACH
  | .kDO
  | .kEACH
  | .kEND
  | .kEXCLUSIVE
  | .kEXPLAIN
  | .kFAIL
  | .kFOR
  | .kIGNORE
  | .kIMMEDIATE
  | .kINITIALLY
  | .kINSTEAD
  | .kLIKE
  | .kGLOB
  | .kREGEXP
  | .kMATCH
  | .kNO
  | .kPLAN
  | .kQUERY
  | .kKEY
  | .kOF
  | .kOFFSET
  | .kPRAGMA
  | .kRAISE
  | .kRECURSIVE
  | .kRELEASE
  | .kREPLACE
  | .kRESTRICT
  | .kROW
  | .kROWS
  | .kROLLBACK
  | .kSAVEPOINT
  | .kTEMP
  | .kTRIGGER
  | .kVACUUM
  | .kVIEW
  | .kVIRTUAL
  | .kWITH
  | .kWITHOUT
  | .kNULLS
  | .kFIRST
  | .kLAST
  | .kCURRENT
  | .kFOLLOWING
  | .kPARTITION
  | .kPRECEDING
  | .kRANGE
  | .kUNBOUNDED
  | .kEXCLUDE
  | .kGROUPS
  | .kOTHERS
  | .kTIES
  | .kGENERATED
  | .kALWAYS
  | .kMATERIALIZED
  | .kREINDEX
  | .kRENAME
  | .kCURRENT_DATE
  | .kCURRENT_TIME
  | .kCURRENT_TIMESTAMP
  | .kIF
  | .kFILTER
  | .kOVER
  | .kWINDOW
  | .kINDEXED => true
  | _ => false

/-- JOIN_KW: usable as a name (`nm`) but not as an expression identifier. -/
def TK.isJoinKw : TK → Bool
  | .kCROSS | .kFULL | .kINNER | .kLEFT | .kNATURAL | .kOUTER | .kRIGHT => true
  | _ => false

structure Token where
  kind : TK
  s : Nat
  e : Nat
  deriving Inhabited

@[inline] def byteAt (s : String) (i : Nat) : UInt8 :=
  if h : (⟨i⟩ : String.Pos.Raw) < s.rawEndPos then s.getUTF8Byte ⟨i⟩ h else 0

/-- The text of bytes [i, j) (token boundaries are always character boundaries). -/
@[inline] def sub (s : String) (i j : Nat) : String := String.Pos.Raw.extract s ⟨i⟩ ⟨j⟩

@[inline] def isDigit (c : UInt8) : Bool := c >= 48 && c <= 57
@[inline] def isAlpha (c : UInt8) : Bool := (c ||| 32) >= 97 && (c ||| 32) <= 122
@[inline] def isXDigit (c : UInt8) : Bool := isDigit c || ((c ||| 32) >= 97 && (c ||| 32) <= 102)
@[inline] def isIdChar (c : UInt8) : Bool := isAlpha c || isDigit c || c == 95 || c == 36 || c >= 128
@[inline] def isIdStart (c : UInt8) : Bool := isAlpha c || c == 95 || c >= 128
@[inline] def isSpace (c : UInt8) : Bool := c == 32 || c == 10 || c == 9 || c == 13 || c == 12

/-- First index >= i whose byte fails p (or the end). -/
@[specialize] def scanWhile (p : UInt8 → Bool) (s : String) (i : Nat) : Nat :=
  if h : i < s.utf8ByteSize then
    if p (byteAt s i) then scanWhile p s (i + 1) else i
  else i
termination_by s.utf8ByteSize - i

def lineEnd (s : String) (i : Nat) : Nat := scanWhile (fun c => c != 10) s i

/-- End of a block comment whose pair of bytes (i-1, i) is examined next; none when unterminated. -/
def blockEnd? (s : String) (i : Nat) : Option Nat :=
  if h : i < s.utf8ByteSize then
    if byteAt s i == 47 && byteAt s (i - 1) == 42 then some (i + 1) else blockEnd? s (i + 1)
  else none
termination_by s.utf8ByteSize - i

/-- As blockEnd?, the end of input when unterminated (sqlite treats it as a comment to the end). -/
def blockEnd (s : String) (i : Nat) : Nat := (blockEnd? s i).getD s.utf8ByteSize

/-- True when the trivia (whitespace, comments) starting at i ends in an unterminated block comment. -/
def openComment (s : String) (i : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    let c := byteAt s i
    if isSpace c then openComment s (i + 1) fuel
    else if c == 45 && byteAt s (i + 1) == 45 then openComment s (lineEnd s (i + 2)) fuel
    else if c == 47 && byteAt s (i + 1) == 42 then
      match blockEnd? s (i + 3) with
      | some e => openComment s e fuel
      | none => true
    else false

/-- Skips whitespace and comments. -/
def skipTrivia (s : String) (i : Nat) : Nat → Nat
  | 0 => i
  | fuel + 1 =>
    let c := byteAt s i
    if isSpace c then skipTrivia s (i + 1) fuel
    else if c == 45 && byteAt s (i + 1) == 45 then skipTrivia s (lineEnd s (i + 2)) fuel
    else if c == 47 && byteAt s (i + 1) == 42 then skipTrivia s (blockEnd s (i + 3)) fuel
    else i

/-- Upper-cases an ASCII letter. -/
@[inline] def up (c : UInt8) : UInt8 := if c >= 97 && c <= 122 then c - 32 else c

def eqFold (kw : String) (s : String) (i : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => byteAt kw k == up (byteAt s (i + k)) && eqFold kw s i k

def kwList : List (String × TK) := [
  ("ABORT", .kABORT),
  ("ACTION", .kACTION),
  ("ADD", .kADD),
  ("AFTER", .kAFTER),
  ("ALL", .kALL),
  ("ALTER", .kALTER),
  ("ALWAYS", .kALWAYS),
  ("ANALYZE", .kANALYZE),
  ("AND", .kAND),
  ("AS", .kAS),
  ("ASC", .kASC),
  ("ATTACH", .kATTACH),
  ("AUTOINCREMENT", .kAUTOINCREMENT),
  ("BEFORE", .kBEFORE),
  ("BEGIN", .kBEGIN),
  ("BETWEEN", .kBETWEEN),
  ("BY", .kBY),
  ("CASCADE", .kCASCADE),
  ("CASE", .kCASE),
  ("CAST", .kCAST),
  ("CHECK", .kCHECK),
  ("COLLATE", .kCOLLATE),
  ("COLUMN", .kCOLUMN),
  ("COMMIT", .kCOMMIT),
  ("CONFLICT", .kCONFLICT),
  ("CONSTRAINT", .kCONSTRAINT),
  ("CREATE", .kCREATE),
  ("CROSS", .kCROSS),
  ("CURRENT", .kCURRENT),
  ("CURRENT_DATE", .kCURRENT_DATE),
  ("CURRENT_TIME", .kCURRENT_TIME),
  ("CURRENT_TIMESTAMP", .kCURRENT_TIMESTAMP),
  ("DATABASE", .kDATABASE),
  ("DEFAULT", .kDEFAULT),
  ("DEFERRED", .kDEFERRED),
  ("DEFERRABLE", .kDEFERRABLE),
  ("DELETE", .kDELETE),
  ("DESC", .kDESC),
  ("DETACH", .kDETACH),
  ("DISTINCT", .kDISTINCT),
  ("DO", .kDO),
  ("DROP", .kDROP),
  ("END", .kEND),
  ("EACH", .kEACH),
  ("ELSE", .kELSE),
  ("ESCAPE", .kESCAPE),
  ("EXCEPT", .kEXCEPT),
  ("EXCLUSIVE", .kEXCLUSIVE),
  ("EXCLUDE", .kEXCLUDE),
  ("EXISTS", .kEXISTS),
  ("EXPLAIN", .kEXPLAIN),
  ("FAIL", .kFAIL),
  ("FILTER", .kFILTER),
  ("FIRST", .kFIRST),
  ("FOLLOWING", .kFOLLOWING),
  ("FOR", .kFOR),
  ("FOREIGN", .kFOREIGN),
  ("FROM", .kFROM),
  ("FULL", .kFULL),
  ("GENERATED", .kGENERATED),
  ("GLOB", .kGLOB),
  ("GROUP", .kGROUP),
  ("GROUPS", .kGROUPS),
  ("HAVING", .kHAVING),
  ("IF", .kIF),
  ("IGNORE", .kIGNORE),
  ("IMMEDIATE", .kIMMEDIATE),
  ("IN", .kIN),
  ("INDEX", .kINDEX),
  ("INDEXED", .kINDEXED),
  ("INITIALLY", .kINITIALLY),
  ("INNER", .kINNER),
  ("INSERT", .kINSERT),
  ("INSTEAD", .kINSTEAD),
  ("INTERSECT", .kINTERSECT),
  ("INTO", .kINTO),
  ("IS", .kIS),
  ("ISNULL", .kISNULL),
  ("JOIN", .kJOIN),
  ("KEY", .kKEY),
  ("LAST", .kLAST),
  ("LEFT", .kLEFT),
  ("LIKE", .kLIKE),
  ("LIMIT", .kLIMIT),
  ("MATCH", .kMATCH),
  ("MATERIALIZED", .kMATERIALIZED),
  ("NATURAL", .kNATURAL),
  ("NO", .kNO),
  ("NOT", .kNOT),
  ("NOTHING", .kNOTHING),
  ("NOTNULL", .kNOTNULL),
  ("NULL", .kNULL),
  ("NULLS", .kNULLS),
  ("OF", .kOF),
  ("OFFSET", .kOFFSET),
  ("ON", .kON),
  ("OR", .kOR),
  ("ORDER", .kORDER),
  ("OTHERS", .kOTHERS),
  ("OUTER", .kOUTER),
  ("OVER", .kOVER),
  ("PARTITION", .kPARTITION),
  ("PLAN", .kPLAN),
  ("PRAGMA", .kPRAGMA),
  ("PRECEDING", .kPRECEDING),
  ("PRIMARY", .kPRIMARY),
  ("QUERY", .kQUERY),
  ("RAISE", .kRAISE),
  ("RANGE", .kRANGE),
  ("RECURSIVE", .kRECURSIVE),
  ("REFERENCES", .kREFERENCES),
  ("REGEXP", .kREGEXP),
  ("REINDEX", .kREINDEX),
  ("RELEASE", .kRELEASE),
  ("RENAME", .kRENAME),
  ("REPLACE", .kREPLACE),
  ("RESTRICT", .kRESTRICT),
  ("RETURNING", .kRETURNING),
  ("RIGHT", .kRIGHT),
  ("ROLLBACK", .kROLLBACK),
  ("ROW", .kROW),
  ("ROWS", .kROWS),
  ("SAVEPOINT", .kSAVEPOINT),
  ("SELECT", .kSELECT),
  ("SET", .kSET),
  ("TABLE", .kTABLE),
  ("TEMP", .kTEMP),
  ("TEMPORARY", .kTEMP),
  ("THEN", .kTHEN),
  ("TIES", .kTIES),
  ("TO", .kTO),
  ("TRANSACTION", .kTRANSACTION),
  ("TRIGGER", .kTRIGGER),
  ("UNBOUNDED", .kUNBOUNDED),
  ("UNION", .kUNION),
  ("UNIQUE", .kUNIQUE),
  ("UPDATE", .kUPDATE),
  ("USING", .kUSING),
  ("VACUUM", .kVACUUM),
  ("VALUES", .kVALUES),
  ("VIEW", .kVIEW),
  ("VIRTUAL", .kVIRTUAL),
  ("WHEN", .kWHEN),
  ("WHERE", .kWHERE),
  ("WINDOW", .kWINDOW),
  ("WITH", .kWITH),
  ("WITHOUT", .kWITHOUT)]

/-- The keywords and their kinds, as parallel arrays indexed by an entry number. -/
def kwWords : Array String := kwList.toArray.map (·.1)
def kwToks : Array TK := kwList.toArray.map (·.2)

/-- The hash of a keyword (upper-cased first and last byte, and the length): the slot its chain starts in. -/
@[inline] def kwHash (c0 cn : UInt8) (n : Nat) : Nat := ((c0.toNat * 4) ^^^ (cn.toNat * 7) ^^^ n) % 256

/-- Hash chains: slot h holds 1 + the first entry of its chain (0: empty); `next` links an entry to 1 + the following one. -/
def kwChains : Array Nat × Array Nat :=
  (List.range kwWords.size).foldl (fun (slots, next) e =>
    let w := kwWords.getD e ""
    let h := kwHash (byteAt w 0) (byteAt w (w.utf8ByteSize - 1)) w.utf8ByteSize
    (slots.setIfInBounds h (e + 1), next.push (slots.getD h 0))) (Array.replicate 256 0, #[])

/-- The keyword spelled by bytes [i, j) of s, in any case; `.id` when it is none. -/
def kwLookup (s : String) (i j : Nat) : TK :=
  let n := j - i
  if n < 2 || n > 17 then .id
  else
    let c := byteAt s i
    if !isAlpha c then .id
    else go n (kwChains.1.getD (kwHash (up c) (up (byteAt s (j - 1))) n) 0) kwWords.size
where
  go (n : Nat) : Nat → Nat → TK
    | _, 0 => .id
    | 0, _ => .id
    | e + 1, f + 1 =>
      let w := kwWords.getD e ""
      if w.utf8ByteSize == n && eqFold w s i n then kwToks.getD e .id else go n (kwChains.2.getD e 0) f

/-- The keywords sqlite3_complete tells apart (EXPLAIN, CREATE, TEMP, TRIGGER, END); `.id` for any other word. -/
def kwClass (s : String) (i j : Nat) : TK :=
  let n := j - i
  let c := up (byteAt s i)
  if n == 3 then (if c == 69 && eqFold "END" s i 3 then .kEND else .id)
  else if n == 4 then (if c == 84 && eqFold "TEMP" s i 4 then .kTEMP else .id)
  else if n == 6 then (if c == 67 && eqFold "CREATE" s i 6 then .kCREATE else .id)
  else if n == 7 then
    (if c == 69 && eqFold "EXPLAIN" s i 7 then .kEXPLAIN else if c == 84 && eqFold "TRIGGER" s i 7 then .kTRIGGER else .id)
  else if n == 9 then (if c == 84 && eqFold "TEMPORARY" s i 9 then .kTEMP else .id)
  else .id

/-- Index after the quoted run starting at i (byte q at i): handles the doubled-quote escape; none when unterminated. -/
def quotedEnd (s : String) (q : UInt8) (i : Nat) : Option Nat :=
  go (i + 1)
where
  go (j : Nat) : Option Nat :=
    if h : j < s.utf8ByteSize then
      if byteAt s j == q then
        if byteAt s (j + 1) == q then go (j + 2) else some (j + 1)
      else go (j + 1)
    else none
  termination_by s.utf8ByteSize - j

/-- True when every `_` in [i, j) sits between two digits (hex digits for a hex literal). -/
def sepsOk (hex : Bool) (s : String) (i j : Nat) : Bool :=
  go i (j - i)
where
  go (k : Nat) : Nat → Bool
    | 0 => true
    | f + 1 =>
      if byteAt s k == 95 then
        let ok := fun c => if hex then isXDigit c else isDigit c
        k > i && ok (byteAt s (k - 1)) && ok (byteAt s (k + 1)) && go (k + 1) f
      else go (k + 1) f

/-- Lexes the number starting at i (a digit, or a '.' followed by a digit). -/
def lexNumber (s : String) (i : Nat) : Token :=
  let j0 := scanWhile isDigit s i
  let c := byteAt s j0
  -- a plain integer: nothing that continues a number or a word follows the digits
  if j0 > i && !isIdChar c && c != 46 then ⟨.int, i, j0⟩ else
  let c1 := byteAt s (i + 1)
  let (kind, j) : TK × Nat :=
    if byteAt s i == 48 && (c1 ||| 32) == 120 && isXDigit (byteAt s (i + 2)) then
      (.hex, scanWhile (fun c => isXDigit c || c == 95) s (i + 3))
    else
      let j := scanWhile (fun c => isDigit c || c == 95) s i
      let (k1, j) : TK × Nat :=
        if byteAt s j == 46 then (.real, scanWhile (fun c => isDigit c || c == 95) s (j + 1)) else (.int, j)
      let e := byteAt s j
      let d1 := byteAt s (j + 1)
      if (e ||| 32) == 101 && (isDigit d1 || ((d1 == 43 || d1 == 45) && isDigit (byteAt s (j + 2)))) then
        (.real, scanWhile (fun c => isDigit c || c == 95) s (j + 2))
      else (k1, j)
  let j2 := scanWhile isIdChar s j
  if j2 > j then ⟨.illegal, i, j2⟩
  else if !(sepsOk (kind == .hex) s i j) then ⟨.illegal, i, j⟩
  else ⟨kind, i, j⟩

/-- Lexes the token that starts at i (no whitespace skipping); `kw` classifies the word at [i, j). -/
@[specialize] def lexAtG (kw : String → Nat → Nat → TK) (s : String) (i : Nat) : Token :=
  let n := s.utf8ByteSize
  if i >= n then ⟨.eof, n, n⟩ else
  let c := byteAt s i
  let c1 := byteAt s (i + 1)
  let t (k : TK) (len : Nat) : Token := ⟨k, i, i + len⟩
  match c with
  | 59 => t .semi 1
  | 44 => t .comma 1
  | 40 => t .lp 1
  | 41 => t .rp 1
  | 42 => t .star 1
  | 47 => t .slash 1
  | 37 => t .rem 1
  | 43 => t .plus 1
  | 126 => t .bitnot 1
  | 38 => t .bitand 1
  | 45 => if c1 == 62 then (if byteAt s (i + 2) == 62 then t .ptr2 3 else t .ptr 2) else t .minus 1
  | 124 => if c1 == 124 then t .concat 2 else t .bitor 1
  | 61 => if c1 == 61 then t .eq 2 else t .eq 1
  | 33 => if c1 == 61 then t .ne 2 else t .illegal 1
  | 60 => if c1 == 61 then t .le 2 else if c1 == 62 then t .ne 2 else if c1 == 60 then t .shl 2 else t .lt 1
  | 62 => if c1 == 61 then t .ge 2 else if c1 == 62 then t .shr 2 else t .gt 1
  | 46 => if isDigit c1 then lexNumber s i else t .dot 1
  | 39 => match quotedEnd s 39 i with
    | some e => ⟨.str, i, e⟩
    | none => ⟨.illegal, i, n⟩
  | 34 => match quotedEnd s 34 i with
    | some e => ⟨.dqid, i, e⟩
    | none => ⟨.illegal, i, n⟩
  | 96 => match quotedEnd s 96 i with
    | some e => ⟨.qid, i, e⟩
    | none => ⟨.illegal, i, n⟩
  | 91 =>
    let j := scanWhile (fun c => c != 93) s (i + 1)
    if j < n then ⟨.qid, i, j + 1⟩ else ⟨.illegal, i, n⟩
  | 63 => ⟨.param, i, scanWhile isDigit s (i + 1)⟩
  | 58 | 64 | 36 =>
    let j := scanWhile isIdChar s (i + 1)
    if j == i + 1 then t .illegal 1 else ⟨.param, i, j⟩
  | _ =>
    if isDigit c then lexNumber s i
    else if (c ||| 32) == 120 && c1 == 39 then
      let j := scanWhile isXDigit s (i + 2)
      if byteAt s j == 39 && (j - i) % 2 == 0 then ⟨.blob, i, j + 1⟩
      else
        let j2 := scanWhile (fun c => c != 39) s j
        ⟨.illegal, i, if j2 < n then j2 + 1 else n⟩
    else if isIdStart c then
      let j := scanWhile isIdChar s (i + 1)
      ⟨kw s i j, i, j⟩
    else t .illegal 1

def lexAt (s : String) (i : Nat) : Token := lexAtG kwLookup s i

/-- The next token at or after i, skipping whitespace and comments. -/
def lexTok (s : String) (i : Nat) : Token :=
  lexAt s (skipTrivia s i (s.utf8ByteSize + 1))

/-- As lexTok, but only the keywords sqlite3_complete cares about are told from plain words. -/
def lexTokC (s : String) (i : Nat) : Token :=
  lexAtG kwClass s (skipTrivia s i (s.utf8ByteSize + 1))

/-- sqlite3_complete's state machine (complete.c): the shell's line_is_complete. States: 0 nothing seen, 1 start of a statement
(the only complete one), 2 normal, 3 EXPLAIN, 4 CREATE [TEMP], 5 inside a CREATE TRIGGER, 6 saw `;` in a trigger, 7 saw `; END`. -/
def completeStep (state : Nat) (k : TK) : Nat :=
  -- token classes: 0 ';', 1 other, 2 EXPLAIN, 3 CREATE, 4 TEMP, 5 TRIGGER, 6 END
  let c : Nat := match k with
    | .semi => 0
    | .kEXPLAIN => 2
    | .kCREATE => 3
    | .kTEMP => 4
    | .kTRIGGER => 5
    | .kEND => 6
    | _ => 1
  match state with
  | 0 | 1 => if c == 0 then 1 else if c == 2 then 3 else if c == 3 then 4 else 2
  | 2 => if c == 0 then 1 else 2
  | 3 => if c == 0 then 1 else if c == 3 then 4 else if c == 1 then 3 else 2
  | 4 => if c == 0 then 1 else if c == 4 then 4 else if c == 5 then 5 else 2
  | 5 => if c == 0 then 6 else 5
  | 6 => if c == 0 then 6 else if c == 6 then 7 else 5
  | _ => if c == 0 then 1 else 5

/-- The shell's line_is_complete (sqlite3_complete): the text ends a statement with `;`, a CREATE TRIGGER with `; END;`, and no
comment or quoted name is left open. -/
def isComplete (src : String) : Bool :=
  go 0 0 (src.utf8ByteSize + 1)
where
  go (i : Nat) (state : Nat) : Nat → Bool
    | 0 => state == 1
    | f + 1 =>
      let t := lexTokC src i
      match t.kind with
      | .eof => state == 1 && !openComment src i (src.utf8ByteSize + 1)
      | k => go t.e (completeStep state k) f


/-! Every keyword is read back from its text, in either case; the shell's complete-statement scan sees the same five. -/
#guard kwList.all fun (w, k) => kwLookup w 0 w.utf8ByteSize == k && kwLookup w.toLower 0 w.utf8ByteSize == k
#guard kwList.all fun (w, k) =>
  completeStep 3 (kwClass w 0 w.utf8ByteSize) == completeStep 3 k && completeStep 4 (kwClass w.toLower 0 w.utf8ByteSize) == completeStep 4 k
    && completeStep 5 (kwClass w 0 w.utf8ByteSize) == completeStep 5 k && completeStep 6 (kwClass w 0 w.utf8ByteSize) == completeStep 6 k
    && completeStep 7 (kwClass w 0 w.utf8ByteSize) == completeStep 7 k && completeStep 2 (kwClass w 0 w.utf8ByteSize) == completeStep 2 k
#guard kwLookup "selects" 0 7 == .id && kwLookup "x" 0 1 == .id && kwLookup "SELEC" 0 5 == .id && kwLookup "Current_Timestamp" 0 17 == .kCURRENT_TIMESTAMP
#guard isComplete "create trigger t after insert on a begin select 1; end;" && !isComplete "create trigger t after insert on a begin select 1; end"
#guard isComplete "select 1; -- x\n" && !isComplete "select 'a;" && isComplete "explain select 1;" && !isComplete "select 1"

end LSql.Lex