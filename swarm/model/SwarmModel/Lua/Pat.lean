import SwarmModel.Lua.Num

/-! Lua 5.1 patterns, after lstrlib.c's matcher (`match`, `max_expand`, `min_expand`, `%b`, `%f`, back-references).
Recursion runs on fuel: running out is the error lstrlib.c gives for a pattern too complex (its C stack). -/

namespace Swarm.Lua.Pat

/-- a capture: its start, and its length, `none` while open; `pos` for a position capture `()` -/
inductive Len where | open_ | pos | len (n : Nat)
  deriving Inhabited, BEq

structure Cap where
  start : Nat
  len : Len
  deriving Inhabited

abbrev R := Except String

def at_ (a : Array Char) (i : Nat) : Char := a.getD i '\x00'

def isLower (c : Char) := 'a' ≤ c && c ≤ 'z'
def isUpper (c : Char) := 'A' ≤ c && c ≤ 'Z'
def isAlpha (c : Char) := isLower c || isUpper c
def isDigit (c : Char) := '0' ≤ c && c ≤ '9'
def isSpace (c : Char) := c == ' ' || ('\t' ≤ c && c ≤ '\r')
def isCntrl (c : Char) := c.toNat < 32 || c.toNat == 127
def isPunct (c : Char) := 33 ≤ c.toNat && c.toNat ≤ 126 && !isAlpha c && !isDigit c
def isXDigit (c : Char) := isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
def toLower (c : Char) : Char := if isUpper c then Char.ofNat (c.toNat + 32) else c

/-- `%x` class: c is the letter after `%` -/
def classMatch (c cl : Char) : Bool :=
  let r := match toLower cl with
    | 'a' => isAlpha c | 'c' => isCntrl c | 'd' => isDigit c | 'l' => isLower c | 's' => isSpace c
    | 'u' => isUpper c | 'w' => isAlpha c || isDigit c | 'x' => isXDigit c | 'p' => isPunct c
    | 'z' => c.toNat == 0
    | _ => cl == c
  match toLower cl with
  | 'a' | 'c' | 'd' | 'l' | 's' | 'u' | 'w' | 'x' | 'p' | 'z' => if isUpper cl then !r else r
  | _ => r

/-- the index just past the single-character class at p[i] (lstrlib.c's classEnd) -/
def classEnd (p : Array Char) (i : Nat) : R Nat :=
  let c := at_ p i
  if c == '%' then
    if i + 1 ≥ p.size then .error "malformed pattern (ends with '%')" else .ok (i + 2)
  else if c == '[' then
    let j := if at_ p (i + 1) == '^' then i + 2 else i + 1
    -- do { c = p[j++]; if c is % and more follows, j++ } while p[j] != ']'
    let rec go (j : Nat) (fuel : Nat) : R Nat :=
      match fuel with
      | 0 => .error "malformed pattern (missing ']')"
      | fuel + 1 =>
        if j ≥ p.size then .error "malformed pattern (missing ']')" else
        let j' := if at_ p j == '%' && j + 1 < p.size then j + 2 else j + 1
        if j' < p.size && at_ p j' == ']' then .ok (j' + 1) else go j' fuel
    go j (p.size + 1)
  else .ok (i + 1)

/-- c in the set p[i..ec], where p[i] = '[' and p[ec] = ']' (lstrlib.c's matchbracketclass) -/
def matchBracket (c : Char) (p : Array Char) (i ec : Nat) : Bool :=
  let sig := at_ p (i + 1) != '^'
  let q := if sig then i else i + 1
  -- while (++q < ec)
  let rec go (q : Nat) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => !sig
    | fuel + 1 =>
      let q := q + 1
      if q ≥ ec then !sig
      else if at_ p q == '%' then (if classMatch c (at_ p (q + 1)) then sig else go (q + 1) fuel)
      else if at_ p (q + 1) == '-' && q + 2 < ec then
        (if at_ p q ≤ c && c ≤ at_ p (q + 2) then sig else go (q + 2) fuel)
      else if at_ p q == c then sig else go q fuel
  go q (p.size + 1)

def singleMatch (c : Char) (p : Array Char) (i ep : Nat) : Bool :=
  match at_ p i with
  | '.' => true
  | '%' => classMatch c (at_ p (i + 1))
  | '[' => matchBracket c p i (ep - 1)
  | d => d == c

structure MS where
  s : Array Char
  p : Array Char

def captureToClose (caps : Array Cap) : R Nat :=
  let rec go (k : Nat) : R Nat :=
    match k with
    | 0 => .error "invalid pattern capture"
    | k + 1 => if (caps.getD k default).len == .open_ then .ok k else go k
  go caps.size

def checkCapture (caps : Array Cap) (l : Char) : R Nat :=
  let k := l.toNat - '1'.toNat
  if l.toNat < '1'.toNat || k ≥ caps.size || (caps.getD k default).len == .open_ then .error "invalid capture index"
  else .ok k

mutual
/-- `match`: the end of a match of p[pi..] at s[si..], with the captures -/
def doMatch (ms : MS) (fuel : Nat) (si pi : Nat) (caps : Array Cap) : R (Option (Nat × Array Cap)) :=
  match fuel with
  | 0 => .error "pattern too complex"
  | fuel + 1 =>
  let s := ms.s; let p := ms.p
  if pi ≥ p.size then .ok (some (si, caps)) else
  match at_ p pi with
  | '(' =>
    if caps.size ≥ 32 then .error "too many captures" else
    if at_ p (pi + 1) == ')' then doMatch ms fuel si (pi + 2) (caps.push ⟨si, .pos⟩)
    else doMatch ms fuel si (pi + 1) (caps.push ⟨si, .open_⟩)
  | ')' => do
    let k ← captureToClose caps
    let c := caps.getD k default
    doMatch ms fuel si (pi + 1) (caps.set! k ⟨c.start, .len (si - c.start)⟩)
  | '$' =>
    if pi + 1 == p.size then .ok (if si == s.size then some (si, caps) else none)
    else dflt ms fuel si pi caps
  | '%' =>
    match at_ p (pi + 1) with
    | 'b' =>
      if pi + 3 ≥ p.size then .error "unbalanced pattern" else
      let b := at_ p (pi + 2); let e := at_ p (pi + 3)
      if si ≥ s.size || at_ s si != b then .ok none else
      -- the balanced end
      let rec bal (j : Nat) (cont : Nat) (fuel : Nat) : Option Nat :=
        match fuel with
        | 0 => none
        | fuel + 1 =>
          if j ≥ s.size then none
          else if at_ s j == e then (if cont == 1 then some (j + 1) else bal (j + 1) (cont - 1) fuel)
          else if at_ s j == b then bal (j + 1) (cont + 1) fuel
          else bal (j + 1) cont fuel
      match bal (si + 1) 1 (s.size + 1) with
      | some j => doMatch ms fuel j (pi + 4) caps
      | none => .ok none
    | 'f' => do
      let pi' := pi + 2
      if at_ p pi' != '[' then .error "missing '[' after '%f' in pattern" else
      let ep ← classEnd p pi'
      let prev := if si == 0 then '\x00' else at_ s (si - 1)
      let cur := if si < s.size then at_ s si else '\x00'
      if !matchBracket prev p pi' (ep - 1) && matchBracket cur p pi' (ep - 1) then doMatch ms fuel si ep caps else .ok none
    | d =>
      if isDigit d then do
        let k ← checkCapture caps d
        let c := caps.getD k default
        let (ok, n) := match c.len with | .len n => (true, n) | _ => (false, 0)
        let cap := (s.extract c.start (c.start + n))
        if ok && si + n ≤ s.size && s.extract si (si + n) == cap then doMatch ms fuel (si + n) (pi + 2) caps else .ok none
      else dflt ms fuel si pi caps
  | _ => dflt ms fuel si pi caps

/-- a single-character class, maybe with a quantifier -/
def dflt (ms : MS) (fuel : Nat) (si pi : Nat) (caps : Array Cap) : R (Option (Nat × Array Cap)) := do
  match fuel with
  | 0 => .error "pattern too complex"
  | fuel + 1 =>
  let s := ms.s; let p := ms.p
  let ep ← classEnd p pi
  let m := si < s.size && singleMatch (at_ s si) p pi ep
  match at_ p ep with
  | '?' =>
    if m then
      match ← doMatch ms fuel (si + 1) (ep + 1) caps with
      | some r => return some r
      | none => doMatch ms fuel si (ep + 1) caps
    else doMatch ms fuel si (ep + 1) caps
  | '*' => maxExpand ms fuel si pi ep caps
  | '+' => if m then maxExpand ms fuel (si + 1) pi ep caps else return none
  | '-' => minExpand ms fuel si pi ep caps
  | _ => if m then doMatch ms fuel (si + 1) ep caps else return none

def maxExpand (ms : MS) (fuel : Nat) (si pi ep : Nat) (caps : Array Cap) : R (Option (Nat × Array Cap)) :=
  match fuel with
  | 0 => .error "pattern too complex"
  | fuel + 1 =>
  let s := ms.s; let p := ms.p
  -- the most repetitions, then fewer
  let rec count (i : Nat) (k : Nat) : Nat :=
    match k with
    | 0 => i
    | k + 1 => if si + i < s.size && singleMatch (at_ s (si + i)) p pi ep then count (i + 1) k else i
  let n := count 0 (s.size + 1)
  tryDown ms fuel si ep caps n

def tryDown (ms : MS) (fuel : Nat) (si ep : Nat) (caps : Array Cap) (i : Nat) : R (Option (Nat × Array Cap)) :=
  match fuel with
  | 0 => .error "pattern too complex"
  | fuel + 1 => do
    match ← doMatch ms fuel (si + i) (ep + 1) caps with
    | some r => return some r
    | none => match i with
      | 0 => return none
      | i + 1 => tryDown ms fuel si ep caps i

def minExpand (ms : MS) (fuel : Nat) (si pi ep : Nat) (caps : Array Cap) : R (Option (Nat × Array Cap)) :=
  match fuel with
  | 0 => .error "pattern too complex"
  | fuel + 1 => do
    match ← doMatch ms fuel si (ep + 1) caps with
    | some r => return some r
    | none =>
      if si < ms.s.size && singleMatch (at_ ms.s si) ms.p pi ep then minExpand ms fuel (si + 1) pi ep caps
      else return none
end

/-- a capture's value: a string, or a position (1-based) -/
inductive CapVal where | str (s : List Char) | pos (n : Nat)

def getCapture (ms : MS) (caps : Array Cap) (i : Nat) (s e : Nat) : R CapVal :=
  if i ≥ caps.size then
    if i == 0 then .ok (.str (ms.s.extract s e).toList) else .error "invalid capture index"
  else
    let c := caps.getD i default
    match c.len with
    | .open_ => .error "unfinished capture"
    | .pos => .ok (.pos (c.start + 1))
    | .len n => .ok (.str (ms.s.extract c.start (c.start + n)).toList)

/-- the captures of a match from s to e (the whole match if there are none, when `whole`) -/
def captures (ms : MS) (caps : Array Cap) (s e : Nat) (whole : Bool) : R (List CapVal) :=
  let n := if caps.size == 0 && whole then 1 else caps.size
  (List.range n).mapM fun i => getCapture ms caps i s e

def fuelFor (s p : Nat) : Nat := 4 * (s + 2) * (p + 2) + 1000

/-- the first match at or after init (0-based): its start, end and captures; an anchored pattern tries only init -/
def find (s p : List Char) (init : Nat) : R (Option (Nat × Nat × Array Cap)) :=
  let sa := s.toArray
  let anchor := p.head? == some '^'
  let pa := (if anchor then p.tail else p).toArray
  let ms : MS := ⟨sa, pa⟩
  let fuel := fuelFor sa.size pa.size
  let rec go (i : Nat) (k : Nat) : R (Option (Nat × Nat × Array Cap)) :=
    match k with
    | 0 => .ok none
    | k + 1 => do
      match ← doMatch ms fuel i 0 #[] with
      | some (e, caps) => return some (i, e, caps)
      | none => if anchor || i ≥ sa.size then return none else go (i + 1) k
  go init (sa.size + 2)

/-- the index of the first occurrence of the plain string p in s at or after init (0-based) -/
def findPlain (s p : List Char) (init : Nat) : Option Nat :=
  let rec go (i : Nat) (t : List Char) (k : Nat) : Option Nat :=
    match k with
    | 0 => none
    | k + 1 => if p.isPrefixOf t then some i else match t with
      | [] => none
      | _ :: t => go (i + 1) t k
  go init (s.drop init) (s.length + 2)

def hasSpecials (p : List Char) : Bool := p.any fun c => "^$*+?.([%-".toList.contains c

end Swarm.Lua.Pat
