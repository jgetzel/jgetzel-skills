namespace SwarmLean

/-- Lua's `%s` class: space, tab, newline, vertical tab, form feed, carriage return. -/
def isSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c'

/-- `s` without leading and trailing whitespace (util.strip). -/
def strip (s : String) : String := String.ofList ((s.toList.dropWhile isSpace).reverse.dropWhile isSpace).reverse

/-- Python truthiness of a text cell: none for NULL and the empty string. -/
def py (o : Option String) : Option String := o.filter (· ≠ "")

/-- Python truthiness of a number cell: none for NULL and 0. -/
def pyI (o : Option Int) : Option Int := o.filter (· ≠ 0)

/-- `math.floor(a / b)`. -/
def fdiv (a b : Int) : Int := Int.fdiv a b

/-- An integer as text (util.d). -/
def d (n : Int) : String := toString n

/-- `s` padded with spaces on the right to `n` bytes (`%-ns`). -/
def padRight (s : String) (n : Nat) : String := s ++ String.ofList (List.replicate (n - s.utf8ByteSize) ' ')

/-- `s` contains `sub`. -/
def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- SQL `s LIKE p || '%'` for a pattern without wildcards: a case-insensitive (ASCII) prefix test. -/
def likePrefix (s p : String) : Bool := s.toLower.startsWith p.toLower

/-- The first `n` characters of `s` (util.cut: by characters, never splitting one). -/
def cut (s : String) (n : Nat) : String := String.ofList (s.toList.take n)

/-- Lua's `tonumber` on an integer text with optional surrounding whitespace and sign (main.lua's int). -/
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

/-- `x` as C's `%g`: six significant digits, no trailing zeros (for the small readings the CLI prints). -/
def fmtG (x : Float) : String :=
  if x == 0 then "0" else
  let e := (Float.floor (Float.log10 x.abs)).toInt64.toInt
  if e < -4 || e ≥ 6 then fixed x 6 else
  let s := fixed x (5 - e).toNat
  if hasSub s "." then
    let t := String.ofList ((s.toList.reverse.dropWhile (· == '0')).dropWhile (· == '.')).reverse
    t
  else s

/-- util.dur: `90s`, `30m`, `2h` or bare seconds, as seconds. -/
def dur (s : String) : Option Int :=
  let ds := s.toList.takeWhile Char.isDigit
  let rest := s.toList.drop ds.length
  if ds.isEmpty then none else
  let n := (String.ofList ds).toNat?.getD 0
  match rest with
  | [] => some n
  | ['s'] => some n
  | ['m'] => some (n * 60)
  | ['h'] => some (n * 3600)
  | _ => none

/-- Lua's `gmatch("[^,]+")`: the nonempty pieces between commas. -/
def commaPieces (s : String) : List String := (s.splitOn ",").filter (· ≠ "")

/-- util.ago: how long before `now` epoch second `t` was, as `5m` or `2h05m`. -/
def ago (now t : Int) : String :=
  let s := max 0 (now - t)
  if s ≥ 3600 then
    let mm := toString (fdiv (s % 3600) 60)
    s!"{fdiv s 3600}h{if mm.length < 2 then "0" ++ mm else mm}m"
  else s!"{fdiv s 60}m"

/-- The last component of a path (util.basename: Lua's `[^/]*$`). -/
def basename (p : String) : String := (p.splitOn "/").getLastD ""

/-- The path without its last component (util.dirname): "" for a bare name, "/" at the root. -/
def dirname (p : String) : String :=
  match (p.splitOn "/").dropLast with
  | [] => ""
  | [""] => "/"
  | l => "/".intercalate l

/-- os.path.join of two paths (util.join). -/
def joinPath (a b : String) : String :=
  if b.startsWith "/" || a.isEmpty then b else if a.endsWith "/" then a ++ b else a ++ "/" ++ b

/-- Python's `s.split()`: the runs of non-space (util.split with no separator). -/
def words (s : String) : List String :=
  let rec go (cur : List Char) (acc : List String) : List Char → List String
    | [] => (if cur.isEmpty then acc else String.ofList cur.reverse :: acc).reverse
    | c :: cs => if isSpace c then go [] (if cur.isEmpty then acc else String.ofList cur.reverse :: acc) cs
      else go (c :: cur) acc cs
  go [] [] s.toList

/-- util.splitlines: the lines of `s` split at `\n`, a last line without one included, none for "". -/
def splitlines (s : String) : List String :=
  if s.isEmpty then [] else
  let l := s.splitOn "\n"
  if s.endsWith "\n" then l.dropLast else l

/-- util.shquote: as is when only `[%w@%%+=:,./_-]`, else single-quoted. -/
def shquote (s : String) : String :=
  if s != "" && s.toList.all (fun c => c.isAlphanum || "@%+=:,./_-".contains c) then s
  else "'" ++ s.replace "'" "'\"'\"'" ++ "'"

/-- util.shjoin. -/
def shjoin (argv : List String) : String := " ".intercalate (argv.map shquote)


/-- Run in herdr-mods/: the hash of what `herdr-mods install` copies into Herdr, which it writes as the install stamp
and `swarm who` compares to say the copies are stale. -/
def herdrStampCmd : String :=
  "cat herdr-mods ../swarm/lean/SwarmLean/Herdr/Install.lean calendar/* ../swarm/herdr/mods/swarm/swarm.svg ../swarm/herdr/mods/rw-rail/* ../swarm/herdr/mods/rw-bar/* ../swarm/herdr/mods/rw-pane/* ../swarm/herdr/mods/rw-swarm/* ../swarm/herdr/mods/rw-question/* ../swarm/herdr/mods/rw-settings/* | { sha256sum 2>/dev/null || shasum -a 256; }"

end SwarmLean
