import SwarmLean.RealSys
import SwarmLean.Lib.Re
import SwarmLean.Lib.Json
import SwarmLean.Args

/-! hr.lua: the helpers the harness-retro tools share (paths, files, ISO times, Python-style output), on IO. -/

namespace HarnessRetro
open SwarmLean
open Lean (Json)

/-- $HOME, or "". -/
def home : IO String := return (← IO.getEnv "HOME").getD ""

/-- One code point decoded at `i`, with its length, or none for an invalid sequence. -/
def utf8At (b : ByteArray) (i : Nat) : Option (Nat × Nat) :=
  let c0 := b[i]!.toNat
  let cont (k : Nat) : Option Nat :=
    if i + k < b.size && b[i + k]!.toNat &&& 0xC0 == 0x80 then some (b[i + k]!.toNat &&& 0x3F) else none
  if c0 < 0x80 then some (c0, 1)
  else if c0 &&& 0xE0 == 0xC0 then do
    let n := ((c0 &&& 0x1F) <<< 6) ||| (← cont 1)
    if n < 0x80 then none else some (n, 2)
  else if c0 &&& 0xF0 == 0xE0 then do
    let n := ((c0 &&& 0x0F) <<< 12) ||| ((← cont 1) <<< 6) ||| (← cont 2)
    if n < 0x800 || (0xD800 ≤ n && n ≤ 0xDFFF) then none else some (n, 3)
  else if c0 &&& 0xF8 == 0xF0 then do
    let n := ((c0 &&& 0x07) <<< 18) ||| ((← cont 1) <<< 12) ||| ((← cont 2) <<< 6) ||| (← cont 3)
    if n < 0x10000 || n > 0x10FFFF then none else some (n, 4)
  else none

/-- Bytes as text, each invalid byte as U+FFFD (Python's errors="replace", closely). -/
def lossy (b : ByteArray) : String := Id.run do
  if let some s := String.fromUTF8? b then return s
  let mut out := ""
  let mut i := 0
  for _ in [0:b.size] do
    if i ≥ b.size then break
    match utf8At b i with
    | some (n, k) => out := out.push (Char.ofNat n); i := i + k
    | none => out := out.push '�'; i := i + 1
  return out

/-- A file's text, invalid UTF-8 replaced (hr.read), or none. -/
def read (p : String) : IO (Option String) := do
  try return some (lossy (← IO.FS.readBinFile p)) catch _ => return none

/-- A file's size in bytes and its bytes as text (util.slurp, for byte counts). -/
def slurp (p : String) : IO ByteArray := do
  try IO.FS.readBinFile p catch _ => return .empty

/-- What is at a path, following symlinks (lfs's mode). -/
def kind (p : String) : IO Kind := do
  try
    let md ← System.FilePath.metadata p
    return match md.type with | .file => .file | .dir => .dir | .symlink => .link | _ => .other
  catch _ => return .none

/-- A regular file. -/
def isfile (p : String) : IO Bool := return (← kind p) == .file

/-- `s` with every `old` replaced by `new` (str.replace; an empty `old` changes nothing). -/
def plainReplace (s old new : String) : String := if old.isEmpty then s else s.replace old new

/-- `~` and `~/…` with $HOME (os.path.expanduser). -/
def expanduser (h p : String) : String :=
  if p == "~" || p.startsWith "~/" then h ++ (p.drop 1).toString else p

/-- os.path.normpath. -/
def normpath (p : String) : String :=
  let abs := p.startsWith "/"
  let out := (p.splitOn "/").foldl (init := (#[] : Array String)) fun out c =>
    if c == "" || c == "." then out
    else if c == ".." then
      if out.size > 0 && out.back! != ".." then out.pop else if abs then out else out.push c
    else out.push c
  let r := (if abs then "/" else "") ++ "/".intercalate out.toList
  if r == "" then "." else r

/-- os.path.realpath: symlinks resolved as far as the path exists, the rest normalised lexically. -/
partial def realpath (p : String) : IO String := do
  let cwd := (← IO.currentDir).toString
  let p := normpath (if p.startsWith "/" then p else cwd ++ "/" ++ p)
  let rec go (p : String) (rest : List String) : IO String := do
    if let some r ← (try some <$> IO.FS.realPath p catch _ => pure none) then
      return rest.foldl (fun r c => (if r == "/" then "" else r) ++ "/" ++ c) r.toString
    if p == "/" then return p
    let parent := match dirname p with | "" => "/" | d => d
    go parent (basename p :: rest)
  go p []

/-- The names in a directory, hidden ones skipped; none when it can't be read. -/
def names (dir : String) : IO (List String) := do
  try return ((← System.FilePath.readDir dir).toList.map (·.fileName)).filter (!·.startsWith ".")
  catch _ => return []

/-- Files under `dir` (recursive, hidden names skipped, as glob's **) whose name ends in `ext`; sorted. -/
partial def walk (dir : String) (ext : String) (depth : Nat := 0) : IO (List String) := do
  if depth > 20 then return []
  let mut out := #[]
  for n in ← names dir do
    let p := dir ++ "/" ++ n
    match ← kind p with
    | .dir => out := out ++ (← walk p ext (depth + 1))
    | .file => if n.endsWith ext then out := out.push p
    | _ => pure ()
  return out.toList.mergeSort (· ≤ ·)

/-- glob(dir/*/): sorted, without the trailing slash. -/
def subdirs (dir : String) : IO (List String) := do
  let ps := (← names dir).map (dir ++ "/" ++ ·)
  return ((← ps.filterM fun p => return (← kind p) == .dir)).mergeSort (· ≤ ·)

/-- sorted() with a key: stable, ascending. -/
def sortedBy (l : List α) (key : α → Float) : List α := l.mergeSort fun a b => key a ≤ key b

/-- Days from the civil date to 1970-01-01. -/
def days (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := Int.fdiv y 400
  let yoe := y - era * 400
  let doy := Int.fdiv (153 * (m + (if m > 2 then -3 else 9)) + 2) 5 + d - 1
  era * 146097 + yoe * 365 + Int.fdiv yoe 4 - Int.fdiv yoe 100 + doy - 719468

/-- The civil date (y, m, d) of a day count from 1970-01-01 (the inverse of `days`). -/
def civil (z : Int) : Int × Int × Int :=
  let z := z + 719468
  let era := Int.fdiv z 146097
  let doe := z - era * 146097
  let yoe := Int.fdiv (doe - Int.fdiv doe 1460 + Int.fdiv doe 36524 - Int.fdiv doe 146096) 365
  let doy := doe - (365 * yoe + Int.fdiv yoe 4 - Int.fdiv yoe 100)
  let mp := Int.fdiv (5 * doy + 2) 153
  let d := doy - Int.fdiv (153 * mp + 2) 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m, d)

/-- `n` as at least two digits. -/
def two (n : Int) : String := let s := toString n; if s.length < 2 then "0" ++ s else s

/-- os.date("!%Y-%m-%dT%H:%M:%SZ", t). -/
def isoUtc (t : Int) : String :=
  let (y, m, d) := civil (Int.fdiv t 86400)
  let s := t - Int.fdiv t 86400 * 86400
  s!"{y}-{two m}-{two d}T{two (s / 3600)}:{two (s % 3600 / 60)}:{two (s % 60)}Z"

/-- The local zone's offset from UTC at epoch second `t`, in seconds (strftime's %z). -/
def localOffset (t : Int) : IO Int := do
  let z ← Shim.strftime "%z" (Int64.ofInt t)
  let cs := z.toList
  let num (a : List Char) : Int := (String.ofList a).toNat?.getD 0
  match cs with
  | [sg, h1, h2, m1, m2] => return (if sg == '-' then -1 else 1) * (num [h1, h2] * 3600 + num [m1, m2] * 60)
  | _ => return 0

/-- mktime: epoch seconds of a local wall time given as seconds since the epoch read as UTC. -/
def mktime (wall : Int) : IO Int := do
  let t1 := wall - (← localOffset wall)
  return wall - (← localOffset t1)

/-- Digits at the start of `cs`, exactly `n` of them. -/
def digitsN (cs : List Char) (n : Nat) : Option (Nat × List Char) :=
  let ds := cs.take n
  if ds.length == n && ds.all Char.isDigit then some ((String.ofList ds).toNat!, cs.drop n) else none

/-- Seconds since the epoch for an ISO 8601 time; without a zone the time is local (hr.parse_iso). -/
def parseIso (s : String) : IO (Option Float) := do
  let cs := s.toList
  let some (y, cs) := digitsN cs 4 | return none
  let '-' :: cs := cs | return none
  let some (mo, cs) := digitsN cs 2 | return none
  let '-' :: cs := cs | return none
  let some (d, cs) := digitsN cs 2 | return none
  let mut (h, mi, sec, frac, zone) := ((0 : Nat), (0 : Nat), (0 : Nat), (0 : Float), cs)
  if !cs.isEmpty then
    let c :: r := cs | return none
    if c != 'T' && c != ' ' then return none
    let some (hh, r) := digitsN r 2 | return none
    let r' := if r.head? == some ':' then r.tail else r
    match digitsN r' 2 with
    | some (mm, r2) => h := hh; mi := mm; zone := r2
    | none => h := hh; zone := r
    let z' := if zone.head? == some ':' then zone.tail else zone
    if let some (ss, r3) := digitsN z' 2 then
      sec := ss; zone := r3
      if zone.head? == some '.' || zone.head? == some ',' then
        let fr := zone.tail.takeWhile Char.isDigit
        if !fr.isEmpty then
          frac := (parseFloat ("0." ++ String.ofList fr)).getD 0
          zone := zone.tail.drop fr.length
  let base := days y mo d * 86400 + h * 3600 + mi * 60 + sec
  if zone.isEmpty then return some (Float.ofInt (← mktime base) + frac)
  if zone == ['Z'] || zone == ['z'] then return some (Float.ofInt base + frac)
  match zone with
  | sg :: rest =>
    if sg != '+' && sg != '-' then return none
    let some (oh, r) := digitsN rest 2 | return none
    let r := if r.head? == some ':' then r.tail else r
    let some (om, r) := digitsN r 2 | return none
    if !r.isEmpty then return none
    let off : Int := (if sg == '-' then -1 else 1) * (oh * 3600 + om * 60)
    return some (Float.ofInt (base - off) + frac)
  | [] => return none

/-- `x` as C's `%.kf`: a negative that rounds to zero keeps its sign. -/
def cfixed (x : Float) (k : Nat) : String := let s := fixed x k; if x < 0 && !s.startsWith "-" then "-" ++ s else s

/-- `x` as `%w.kf`. -/
def fmtF (x : Float) (w k : Nat) : String := let s := cfixed x k; "".pushn ' ' (w - s.length) ++ s

/-- `n` as `%wd`. -/
def fmtD (n : Int) (w : Nat) : String := let s := toString n; "".pushn ' ' (w - s.length) ++ s

/-- An `Except` from the regex module as IO (a bad pattern is a bug). -/
def ok (e : Except String α) : IO α := IO.ofExcept (e.mapError IO.userError)

/-- Lua's truthiness of a JSON field as the tools test it: present, and not false, "", or 0. -/
def truthy : Option Json → Bool
  | none | some .null | some (.bool false) | some (.str "") => false
  | some (.num n) => n.toFloat != 0
  | _ => true

/-- A JSON object's or array's elements as a list (ipairs over an array; [] otherwise). -/
def arr : Option Json → List Json
  | some (.arr a) => a.toList
  | _ => []

/-- Runs argv; stdout and the exit code (proc.exec). -/
def exec (argv : List String) : IO ProcOut := execIO' argv {}

/-- proc.git: the trimmed stdout, none when git fails. -/
def git (args : List String) : IO (Option String) := do
  let r ← exec ("git" :: args)
  return if r.code == 0 then some (strip r.stdout) else none

/-- Prints an argparse error (exit 2) or help (exit 0); the parse otherwise. -/
def parseArgs (spec : Args.Spec) (args : List String) : IO (Option Args.Parsed) := do
  match Args.parse spec "cmd" "" args with
  | .ok p => return some p
  | .error (.help t) => IO.println t; return none
  | .error (.error e) => IO.eprintln e; IO.Process.exit 2

end HarnessRetro
