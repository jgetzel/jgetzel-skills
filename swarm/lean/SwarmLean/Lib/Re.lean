import SwarmLean.Util

/-! re.lua: Python's re as the Lua runs it on PCRE2 (UTF and UCP, so `\w` matches é), here a backtracking matcher
over the subject's characters. Positions are character indices, 0-based, end exclusive. Supported: literals, `.`,
classes with ranges and `\w \s \d` (and negations), `^ $ \A \z \Z \b \B`, groups (capturing, `(?:`, named,
lookahead `(?=` `(?!`, lookbehind `(?<=` `(?<!`, inline and scoped flags `(?ims)` `(?i:`), alternation, and `* + ? {m,n}` greedy or lazy. -/

namespace SwarmLean.Re

/-- re.S, re.M, re.I. -/
structure Flags where
  S : Bool := false
  M : Bool := false
  I : Bool := false
  deriving Inhabited

/-- re.S. -/
def S : Flags := { S := true }
/-- re.M. -/
def M : Flags := { M := true }
/-- re.I. -/
def I : Flags := { I := true }
/-- The union of two flag sets. -/
def Flags.or (a b : Flags) : Flags := { S := a.S || b.S, M := a.M || b.M, I := a.I || b.I }

-- shortcut: UCP's Unicode classes approximated: non-ASCII is a word character except the common punctuation and
-- symbol blocks below, `\d` is ASCII digits only, and caseless matching folds ASCII only; upgrade with a Unicode
-- table if a pattern meets other scripts' punctuation or digits.
/-- A non-ASCII character that is not a letter, digit or connector (approximately: Latin-1 symbols, the
punctuation, arrow, math, box, shape, dingbat, CJK-punctuation, fullwidth-punctuation and emoji blocks). -/
def nonWordHigh (n : Nat) : Bool :=
  (n < 0xC0 && ![0xAA, 0xB2, 0xB3, 0xB5, 0xB9, 0xBA, 0xBC, 0xBD, 0xBE].contains n) || n == 0xD7 || n == 0xF7 ||
  (0x2000 ≤ n && n ≤ 0x206F && ![0x203F, 0x2040, 0x2054].contains n) || (0x2190 ≤ n && n ≤ 0x23FF) ||
  (0x2500 ≤ n && n ≤ 0x27BF) || (0x2E00 ≤ n && n ≤ 0x2E7F) || (0x3000 ≤ n && n ≤ 0x3004) ||
  (0x3008 ≤ n && n ≤ 0x3020) || n == 0x3030 || (0xFF01 ≤ n && n ≤ 0xFF0F) || (0xFF1A ≤ n && n ≤ 0xFF20) ||
  (0xFF3B ≤ n && n ≤ 0xFF40 && n != 0xFF3F) || (0xFF5B ≤ n && n ≤ 0xFF65) || (0x1F000 ≤ n && n ≤ 0x1FAFF)

/-- `\w`: a letter, digit or underscore. -/
def isWord (c : Char) : Bool := c.isAlphanum || c == '_' || (c.toNat ≥ 0x80 && !nonWordHigh c.toNat)

/-- `\s`: ASCII whitespace and Unicode's spaces and separators. -/
def isSpaceU (c : Char) : Bool :=
  let n := c.toNat
  (9 ≤ n && n ≤ 13) || n == 32 || n == 0x85 || n == 0xA0 || n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) ||
  n == 0x2028 || n == 0x2029 || n == 0x202F || n == 0x205F || n == 0x3000

/-- An item of a `[...]` class. -/
inductive Item
  | ch (c : Char)
  | range (a b : Char)
  | word (neg : Bool)
  | space (neg : Bool)
  | digit (neg : Bool)
  deriving Inhabited

/-- A parsed pattern; the flags that matter are fixed into each node as it is parsed. -/
inductive Node
  | ch (c : Char) (ci : Bool)
  | any (dotall : Bool)
  | cls (neg : Bool) (items : List Item) (ci : Bool)
  | bol (multi : Bool)
  | eol (multi : Bool)
  | bos
  | eos
  | eosNl
  | wordB (neg : Bool)
  | group (idx : Option Nat) (n : Node)
  | look (neg : Bool) (n : Node)
  | lookB (neg : Bool) (n : Node)
  | cat (ns : List Node)
  | alt (ns : List Node)
  | rep (n : Node) (min : Nat) (max : Option Nat) (greedy : Bool)
  deriving Inhabited

/-- A compiled pattern and its number of capturing groups. -/
structure Regex where
  root : Node
  groups : Nat
  deriving Inhabited

/-- Whether one character is in a class item. -/
def Item.has (c : Char) : Item → Bool
  | .ch d => c == d
  | .range a b => a ≤ c && c ≤ b
  | .word n => isWord c != n
  | .space n => isSpaceU c != n
  | .digit n => c.isDigit != n

/-- Folds ASCII case. -/
def low (c : Char) : Char := c.toLower

/-! ### Parsing -/

/-- The parser's state: the pattern, the position, the groups opened so far. -/
structure PS where
  p : Array Char
  i : Nat := 0
  groups : Nat := 0

/-- The parser monad: state, and an error text (re.error). -/
abbrev P := StateT PS (Except String)

/-- The character at the position, if any. -/
def peek : P (Option Char) := do let s ← get; return s.p[s.i]?
/-- The character `k` past the position, if any. -/
def peekAt (k : Nat) : P (Option Char) := do let s ← get; return s.p[s.i + k]?
/-- Moves past `k` characters. -/
def adv (k : Nat := 1) : P Unit := modify fun s => { s with i := s.i + k }

/-- A run of decimal digits at the position, if any. -/
def digits : P (Option Nat) := do
  let mut n : Option Nat := none
  repeat
    match ← peek with
    | some c => if c.isDigit then n := some (n.getD 0 * 10 + (c.toNat - 48)); adv else break
    | none => break
  return n

/-- A hex digit's value. -/
def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48) else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none

/-- `\x` after the `x`: `hh` or `{h…}`. -/
def hexEsc : P Char := do
  if (← peek) == some '{' then
    adv
    let mut n := 0
    repeat
      match ← peek with
      | some '}' => adv; break
      | some c => match hexVal c with
        | some v => n := n * 16 + v; adv
        | none => throw "bad \\x{...} escape"
      | none => throw "bad \\x{...} escape"
    return Char.ofNat n
  let mut n := 0
  for _ in [0:2] do
    match (← peek).bind hexVal with
    | some v => n := n * 16 + v; adv
    | none => break
  return Char.ofNat n

/-- A control or literal escape's character (`\n`, `\t`, `\.` …), or none for a class escape or an assertion. -/
def litEsc (c : Char) (inClass : Bool) : P (Option Char) := do
  match c with
  | 'n' => return some '\n' | 't' => return some '\t' | 'r' => return some '\r'
  | 'f' => return some '\x0c' | 'v' => return some '\x0b' | 'e' => return some '\x1b' | 'a' => return some '\x07'
  | '0' => return some '\x00'
  | 'x' => return some (← hexEsc)
  | 'b' => return if inClass then some '\x08' else none
  | _ =>
    if c.isAlpha then
      if "dDwWsSbBAzZ".toList.contains c then return none
      throw s!"unrecognized character follows \\: {c}"
    if c.isDigit then throw "backreferences are not supported"
    return some c

/-- A class escape `\w \W \s \S \d \D` as an item. -/
def clsEsc (c : Char) : Option Item :=
  match c with
  | 'w' => some (.word false) | 'W' => some (.word true) | 's' => some (.space false) | 'S' => some (.space true)
  | 'd' => some (.digit false) | 'D' => some (.digit true) | _ => none

/-- A `[...]` class after its `[`. -/
partial def parseClass (fl : Flags) : P Node := do
  let neg := (← peek) == some '^'
  if neg then adv
  let mut items : Array Item := #[]
  let mut first := true
  repeat
    let some c ← peek | throw "missing terminating ] for character class"
    if c == ']' && !first then adv; break
    first := false
    adv
    let mut lo : Option Char := some c
    if c == '\\' then
      let some e ← peek | throw "\\ at end of pattern"
      adv
      match clsEsc e with
      | some it => items := items.push it; lo := none
      | none => lo := (← litEsc e true)
    if let some a := lo then
      if (← peek) == some '-' && (← peekAt 1) != some ']' && (← peekAt 1).isSome then
        adv
        let some b ← peek | throw "missing terminating ] for character class"
        adv
        let hi ← if b == '\\' then do
            let some e ← peek | throw "\\ at end of pattern"
            adv
            if (clsEsc e).isSome then throw "invalid range in character class"
            pure ((← litEsc e true).getD e)
          else pure b
        if hi < a then throw "range out of order in character class"
        items := items.push (.range a hi)
      else items := items.push (.ch a)
  return .cls neg items.toList fl.I

/-- Inline flag letters up to `)` or `:`: the flags they turn on (or, after `-`, off). -/
def flagLetters (fl : Flags) : P Flags := do
  let mut f := fl
  let mut on := true
  repeat
    match ← peek with
    | some 'i' => adv; f := { f with I := on }
    | some 's' => adv; f := { f with S := on }
    | some 'm' => adv; f := { f with M := on }
    | some 'x' => throw "the x flag is not supported"
    | some '-' => adv; on := false
    | _ => break
  return f

/-- A quantifier `{m}`, `{m,}`, `{m,n}` or `{,n}` at a `{`, or none (then the `{` is a literal). -/
def braces : P (Option (Nat × Option Nat)) := do
  let s0 ← get
  adv
  let lo ← digits
  let r ← if (← peek) == some '}' then
      pure (lo.map fun n => (n, some n))
    else if (← peek) == some ',' then do
      adv
      let hi ← digits
      if (← peek) == some '}' && (lo.isSome || hi.isSome) then pure (some (lo.getD 0, hi)) else pure none
    else pure none
  match r with
  | some q => adv; return some q
  | none => set s0; return none

mutual

/-- Alternatives up to `)` or the end. -/
partial def parseAlt (fl : Flags) : P Node := do
  let mut alts : Array Node := #[]
  let mut f := fl
  repeat
    let (n, f') ← parseSeq f
    alts := alts.push n
    f := f'
    if (← peek) == some '|' then adv else break
  return if alts.size == 1 then alts[0]! else .alt alts.toList

/-- A sequence of quantified atoms up to `|`, `)` or the end; and the flags an inline `(?i)` left set. -/
partial def parseSeq (fl : Flags) : P (Node × Flags) := do
  let mut ns : Array Node := #[]
  let mut f := fl
  repeat
    let some c ← peek | break
    if c == '|' || c == ')' then break
    if c == '*' || c == '+' || c == '?' then throw "quantifier does not follow a repeatable item"
    match ← parseAtom f with
    | .inl f' => f := f'
    | .inr a =>
      let mut a := a
      let q ← match ← peek with
        | some '*' => adv; pure (some (0, none))
        | some '+' => adv; pure (some (1, none))
        | some '?' => adv; pure (some (0, some 1))
        | some '{' => braces
        | _ => pure none
      if let some (lo, hi) := q then
        if hi.any (· < lo) then throw "numbers out of order in {} quantifier"
        let lazy := (← peek) == some '?'
        -- shortcut: a possessive `+` matches as greedy; no CLI pattern uses one
        if lazy || (← peek) == some '+' then adv
        a := .rep a lo hi !lazy
        if let some x ← peek then
          if x == '*' || x == '+' || x == '?' then throw "quantifier does not follow a repeatable item"
      ns := ns.push a
  return (if ns.size == 1 then ns[0]! else .cat ns.toList, f)

/-- One atom; or, for an inline `(?i)`, the flags it sets. -/
partial def parseAtom (fl : Flags) : P (Sum Flags Node) := do
  let some c ← peek | throw "unexpected end of pattern"
  adv
  match c with
  | '.' => return .inr (.any fl.S)
  | '^' => return .inr (.bol fl.M)
  | '$' => return .inr (.eol fl.M)
  | '[' => return .inr (← parseClass fl)
  | '(' =>
    if (← peek) == some '?' then
      adv
      match ← peek with
      | some ':' => adv; return .inr (.group none (← closeGroup fl))
      | some '=' => adv; return .inr (.look false (← closeGroup fl))
      | some '!' => adv; return .inr (.look true (← closeGroup fl))
      | some '#' =>
        repeat
          match ← peek with
          | some ')' => adv; break
          | some _ => adv
          | none => throw "missing ) after (?# comment"
        return .inl fl
      | some 'P' | some '<' | some '\'' =>
        if (← peek) == some 'P' then adv
        let some o ← peek | throw "unexpected end of pattern"
        if o == '<' && ((← peekAt 1) == some '=' || (← peekAt 1) == some '!') then
          let neg := (← peekAt 1) == some '!'
          adv 2
          return .inr (.lookB neg (← closeGroup fl))
        let close := if o == '<' then '>' else if o == '\'' then '\'' else ' '
        if close == ' ' then throw "unrecognized character after (?P"
        adv
        repeat
          match ← peek with
          | some x => adv; if x == close then break
          | none => throw "syntax error in subpattern name (missing terminator?)"
        let s ← get
        set { s with groups := s.groups + 1 }
        return .inr (.group (some (s.groups + 1)) (← closeGroup fl))
      | _ =>
        let f ← flagLetters fl
        match ← peek with
        | some ')' => adv; return .inl f
        | some ':' => adv; return .inr (.group none (← closeGroup f))
        | _ => throw "unrecognized character after (? or (?-"
    let s ← get
    set { s with groups := s.groups + 1 }
    return .inr (.group (some (s.groups + 1)) (← closeGroup fl))
  | '\\' =>
    let some e ← peek | throw "\\ at end of pattern"
    adv
    match e with
    | 'A' => return .inr .bos
    | 'z' => return .inr .eos
    | 'Z' => return .inr .eosNl
    | 'b' => return .inr (.wordB false)
    | 'B' => return .inr (.wordB true)
    | _ => match clsEsc e with
      | some it => return .inr (.cls false [it] false)
      | none => return .inr (.ch ((← litEsc e false).getD e) fl.I)
  | _ => return .inr (.ch c fl.I)

/-- A group's body and its `)`. -/
partial def closeGroup (fl : Flags) : P Node := do
  let n ← parseAlt fl
  if (← peek) != some ')' then throw "missing closing parenthesis"
  adv
  return n

end

/-- Compiles a pattern; the error is re.error's text. -/
def compile (pat : String) (fl : Flags := {}) : Except String Regex := do
  let (n, s) ← (parseAlt fl).run { p := pat.toList.toArray }
  if s.i < s.p.size then throw "unmatched closing parenthesis"
  return { root := n, groups := s.groups }

/-! ### Matching -/

/-- Captured spans, by group number (0 unused). -/
abbrev Caps := Array (Option (Nat × Nat))

/-- What a match attempt ends with: the end and the captures. -/
abbrev R := Option (Nat × Caps)

mutual

/-- Matches `n` at `i` and then the continuation `k`. -/
partial def go (s : Array Char) (n : Node) (i : Nat) (caps : Caps) (k : Nat → Caps → R) : R :=
  let at? := s[i]?
  let prev := if i == 0 then none else s[i - 1]?
  match n with
  | .ch c ci => match at? with
    | some x => if x == c || (ci && low x == low c) then k (i + 1) caps else none
    | none => none
  | .any dotall => match at? with
    | some x => if dotall || x != '\n' then k (i + 1) caps else none
    | none => none
  | .cls neg items ci => match at? with
    | some x =>
      let hit := items.any (·.has x) || (ci && (items.any (·.has (low x)) || items.any (·.has x.toUpper)))
      if hit != neg then k (i + 1) caps else none
    | none => none
  | .bol multi => if i == 0 || (multi && prev == some '\n' && i < s.size) then k i caps else none
  | .eol multi =>
    if i == s.size || (multi && at? == some '\n') || (i + 1 == s.size && at? == some '\n') then k i caps else none
  | .bos => if i == 0 then k i caps else none
  | .eos => if i == s.size then k i caps else none
  | .eosNl => if i == s.size || (i + 1 == s.size && at? == some '\n') then k i caps else none
  | .wordB neg =>
    let b := (prev.map isWord).getD false != (at?.map isWord).getD false
    if b != neg then k i caps else none
  | .group idx body => go s body i caps fun j c => k j (match idx with | some g => c.set! g (some (i, j)) | none => c)
  | .look neg body =>
    match go s body i caps fun j c => some (j, c) with
    | some (_, c) => if neg then none else k i c
    | none => if neg then k i caps else none
  | .lookB neg body =>
    -- any start at or before i whose match of body ends exactly at i, nearest first
    let hit := (List.range (i + 1)).findSome? fun d => go s body (i - d) caps fun j c => if j == i then some (j, c) else none
    match hit with
    | some (_, c) => if neg then none else k i c
    | none => if neg then k i caps else none
  | .cat ns => goSeq s ns i caps k
  | .alt ns => goAlt s ns i caps k
  | .rep body lo hi greedy => goRep s body lo hi greedy 0 i caps k

/-- Matches the nodes one after another. -/
partial def goSeq (s : Array Char) (ns : List Node) (i : Nat) (caps : Caps) (k : Nat → Caps → R) : R :=
  match ns with
  | [] => k i caps
  | n :: rest => go s n i caps fun j c => goSeq s rest j c k

/-- Tries the alternatives in order. -/
partial def goAlt (s : Array Char) (ns : List Node) (i : Nat) (caps : Caps) (k : Nat → Caps → R) : R :=
  match ns with
  | [] => none
  | n :: rest => match go s n i caps k with
    | some r => some r
    | none => goAlt s rest i caps k

/-- `count` repetitions done; an iteration past the minimum that matches empty ends the loop. -/
partial def goRep (s : Array Char) (body : Node) (lo : Nat) (hi : Option Nat) (greedy : Bool) (count i : Nat)
    (caps : Caps) (k : Nat → Caps → R) : R :=
  let more : Unit → R := fun _ =>
    go s body i caps fun j c => if j == i && count ≥ lo then none else goRep s body lo hi greedy (count + 1) j c k
  if count < lo then more ()
  else if hi.any (count ≥ ·) then k i caps
  else if greedy then match more () with
    | some r => some r
    | none => k i caps
  else match k i caps with
    | some r => some r
    | none => more ()

end

/-- A match: its span and text, and each group's text (none when it did not take part). -/
structure Match where
  s : Nat
  e : Nat
  whole : String
  groups : Array (Option String)
  deriving Inhabited

/-- The `k`th group (1-based), none when unset. -/
def Match.group (m : Match) (k : Nat) : Option String := (m.groups[k - 1]?).join

/-- The characters `a` to `b` of `s`. -/
def slice (s : Array Char) (a b : Nat) : String := String.ofList (s.extract a b).toList

/-- The first match starting at or after `init` (rex's exec). -/
def exec (r : Regex) (s : Array Char) (init : Nat := 0) : Option Match := Id.run do
  for st in [init:s.size + 1] do
    if let some (e, c) := go s r.root st (Array.replicate (r.groups + 1) none) fun j c => some (j, c) then
      return some { s := st, e, whole := slice s st e,
                    groups := (List.range r.groups).toArray.map fun g => c[g + 1]!.map fun (a, b) => slice s a b }
  return none

/-- re.search. -/
def search (pat s : String) (fl : Flags := {}) : Except String (Option Match) :=
  return exec (← compile pat fl) s.toList.toArray

/-- re.match: anchored at the start only. -/
def «match» (pat s : String) (fl : Flags := {}) : Except String (Option Match) := search ("\\A(?:" ++ pat ++ ")") s fl

/-- re.fullmatch: `\z`, not `$`, which also matches before a final newline. -/
def fullmatch (pat s : String) (fl : Flags := {}) : Except String (Option Match) :=
  search ("\\A(?:" ++ pat ++ ")\\z") s fl

/-- The non-overlapping matches, as finditer; an empty match moves on one character. -/
def finditer (pat s : String) (fl : Flags := {}) : Except String (List Match) := do
  let r ← compile pat fl
  let cs := s.toList.toArray
  let mut out : Array Match := #[]
  let mut init := 0
  for _ in [0:cs.size + 2] do
    if init > cs.size then break
    let some m := exec r cs init | break
    out := out.push m
    init := if m.e ≤ m.s then m.s + 1 else m.e
  return out.toList

/-- re.findall: per match its whole text with no groups, its group with one, else every group ("" if unset). -/
def findall (pat s : String) (fl : Flags := {}) : Except String (List (List String)) := do
  return (← finditer pat s fl).map fun m =>
    if m.groups.isEmpty then [m.whole] else m.groups.toList.map (·.getD "")

/-- re.sub with a literal replacement (no backreferences). -/
def sub (pat repl s : String) (fl : Flags := {}) : Except String String := do
  let cs := s.toList.toArray
  let mut out := ""
  let mut last := 0
  for m in ← finditer pat s fl do
    out := out ++ slice cs last m.s ++ repl
    last := m.e
  return out ++ slice cs last cs.size

/-- re.escape: every ASCII character but letters, digits and `_` gets a backslash. -/
def escape (s : String) : String :=
  String.join (s.toList.map fun c => if c.toNat < 128 && !(c.isAlphanum || c == '_') then "\\" ++ c.toString else c.toString)

end SwarmLean.Re
