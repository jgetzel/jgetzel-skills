/-! The few string helpers `claim` needs, duplicated from swarm's `Util` so this package depends on nothing of swarm.
shortcut: a dozen lines copied, merge them if swarm ever imports them from here. -/

namespace Claims

/-- Lua's `%s` class: space, tab, newline, vertical tab, form feed, carriage return. -/
def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'

/-- `s` without leading and trailing whitespace. -/
def strip (s : String) : String := String.ofList ((s.toList.dropWhile isSpace).reverse.dropWhile isSpace).reverse

/-- An integer text with optional surrounding whitespace and sign. -/
def parseInt (s : String) : Option Int :=
  let t := strip s
  let (neg, body) := if t.startsWith "-" then (true, t.drop 1 |>.toString) else if t.startsWith "+" then (false, t.drop 1 |>.toString) else (false, t)
  if body.isEmpty || !body.all Char.isDigit then none
  else body.toNat?.map fun n => if neg then -(n : Int) else n

/-- A decimal like `12.34` or `5` as a float. -/
def parseFloat (s : String) : Option Float :=
  match s.splitOn "." with
  | [a] => a.toNat?.map Float.ofNat
  | [a, b] =>
    if (a.isEmpty && b.isEmpty) || !(a.all Char.isDigit && b.all Char.isDigit) then none
    else some (Float.ofScientific ((a ++ b).toNat?.getD 0) true b.length)
  | _ => none

/-- `x` rounded to `k` decimals as text (`%.kf`). -/
def fixed (x : Float) (k : Nat) : String :=
  let neg := x < 0
  let m := (Float.round (x.abs * Float.ofNat (10 ^ k))).toUInt64.toNat
  let ip := m / 10 ^ k
  let fp := toString (m % 10 ^ k)
  let fs := if k = 0 then "" else "." ++ String.ofList (List.replicate (k - fp.length) '0') ++ fp
  (if neg && m ≠ 0 then "-" else "") ++ toString ip ++ fs

/-- Python's `s.split()`: the runs of non-space. -/
def words (s : String) : List String :=
  let rec go (cur : List Char) (acc : List String) : List Char → List String
    | [] => (if cur.isEmpty then acc else String.ofList cur.reverse :: acc).reverse
    | c :: cs => if isSpace c then go [] (if cur.isEmpty then acc else String.ofList cur.reverse :: acc) cs
      else go (c :: cur) acc cs
  go [] [] s.toList

/-- The lines of `s` split at `\n`, a last line without one included, none for "". -/
def splitlines (s : String) : List String :=
  if s.isEmpty then [] else
  let l := s.splitOn "\n"
  if s.endsWith "\n" then l.dropLast else l

/-- As is when only `[A-Za-z0-9@%+=:,./_-]`, else single-quoted. -/
def shquote (s : String) : String :=
  if s != "" && s.toList.all (fun c => c.isAlphanum || "@%+=:,./_-".contains c) then s
  else "'" ++ s.replace "'" "'\"'\"'" ++ "'"

end Claims
