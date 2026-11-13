import SwarmLean.Lib.Json
import SwarmLean.Util

/-! `herdr-mods events`: today's and tomorrow's events from a Google Calendar secret iCal address, as JSON for the
Calendar panel (was herdr-mods/calendar/events.lua; Lua patterns are ported as the scanners below).
  herdr-mods events [--ics FILE] [--date YYYY-MM-DD]     --test runs the self-test
Config, every key optional: <Herdr app home>/calendar.json
  url_command       a shell command that prints the secret iCal address. Default: the macOS Keychain
                    (security find-generic-password -s herdr-gcal-ics -w), on Linux the Secret Service
                    (secret-tool lookup service herdr-gcal-ics).
  internal_domains  guests outside these domains get "external": true; unset, nobody does.
Exit 3: no address configured. A rule or time zone it can't read is skipped with a line on stderr, which the panel
shows. -/

namespace SwarmLean.Herdr.Events
open Lean (Json)

@[extern "swarm_set_tz"] opaque setTz (tz : @& String) (unset : Bool) : IO Unit
@[extern "swarm_mktime"] opaque mktime (y mo d h mi s : Int64) : IO Int64
@[extern "swarm_strftime"] opaque strftime (fmt : @& String) (t : Int64) : IO String
@[extern "swarm_now"] opaque now : IO UInt64

/-- The user's TZ (none: unset), which local time means. -/
initialize origTz : IO.Ref (Option String) ← IO.mkRef none
initialize warned : IO.Ref (Array String) ← IO.mkRef #[]

def warn (msg : String) : IO Unit := do
  unless (← warned.get).contains msg do
    warned.modify (·.push msg); IO.eprintln msg

-- Calendar days as day numbers since 1970-01-01 (proleptic Gregorian). Int's / and % floor for a positive divisor.
def days (y m d : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := y / 400
  let yoe := y - era * 400
  let doy := (153 * (if m > 2 then m - 3 else m + 9) + 2) / 5 + d - 1
  era * 146097 + yoe * 365 + yoe / 4 - yoe / 100 + doy - 719468

def civil (z : Int) : Int × Int × Int :=
  let z := z + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let m := if mp < 10 then mp + 3 else mp - 9
  (yoe + era * 400 + (if m ≤ 2 then 1 else 0), m, doy - (153 * mp + 2) / 5 + 1)

def wday (z : Int) : Int := (z + 4) % 7 -- 0 = Sunday
def dim (y m : Int) : Int := if m == 12 then 31 else days y (m + 1) 1 - days y m 1

def pad (n : Int) (w : Nat) : String :=
  let s := toString n.natAbs
  (if n < 0 then "-" else "") ++ String.ofList (List.replicate (w - s.length) '0') ++ s

/-- Day `z` as `YYYY-MM-DD` (os.date("!%Y-%m-%d")), or with another separator. -/
def ymd (z : Int) (sep := "-") : String := let (y, m, d) := civil z; s!"{pad y 4}{sep}{pad m 2}{sep}{pad d 2}"

def hhmmss (s : Int) (sep := "") : String := s!"{pad (s / 3600) 2}{sep}{pad (s / 60 % 60) 2}{sep}{pad (s % 60) 2}"

-- Time zones go through the process TZ and the system zoneinfo, so no tz database ships here.
def inTz (tz : Option String) (f : IO α) : IO α := do
  let mut tz := tz
  if let some z := tz then
    let dir := ((← IO.getEnv "TZDIR").getD "/usr/share/zoneinfo") ++ "/"
    unless ← System.FilePath.pathExists (dir ++ z) do
      warn s!"unknown time zone {z}, read as UTC"; tz := some "UTC"
  let orig ← origTz.get
  let set (z : Option String) : IO Unit := setTz (z.getD "") z.isNone
  set (tz <|> orig)
  let r ← f
  set orig
  return r

inductive Kind | date | utc | tz | float
  deriving BEq, Inhabited

/-- A DATE or DATE-TIME: day number, seconds into that day, and its frame: date, utc, tz (TZID) or float (local). -/
structure Dt where
  day : Int
  sec : Int := 0
  kind : Kind := .date
  tz : Option String := none
  deriving Inhabited

abbrev Params := List (String × String)

/-- A parameter; the list holds the last of a repeated one first. -/
def param (ps : Params) (k : String) : Option String := (ps.find? (·.1 == k)).map (·.2)

def digits (cs : List Char) : Option Int :=
  if !cs.isEmpty && cs.all Char.isDigit then (String.ofList cs).toNat?.map Int.ofNat else none

def valueDt (v : String) (params : Params) : Option Dt := do
  let cs := v.toList
  let y ← digits (cs.take 4); let m ← digits ((cs.drop 4).take 2); let d ← digits ((cs.drop 6).take 2)
  if cs.length < 8 then none
  let x : Dt := { day := days y m d }
  match cs.drop 8 with
  | [] => some x
  | 'T' :: r =>
    let (t, z) := (r.take 6, r.drop 6)
    if t.length != 6 || !(z == [] || z == ['Z']) then none
    let h ← digits (t.take 2); let mi ← digits ((t.drop 2).take 2); let s ← digits (t.drop 4)
    let kind := if z == ['Z'] then Kind.utc else if (param params "TZID").isSome then .tz else .float
    some { x with sec := h * 3600 + mi * 60 + s, kind, tz := if kind == .tz then param params "TZID" else none }
  | _ => none

/-- x's wall clock on day (default its own) as Unix seconds. -/
def epoch (x : Dt) (day? : Option Int := none) : IO Int := do
  let day := day?.getD x.day
  if x.kind == .utc then return day * 86400 + x.sec
  let (y, m, d) := civil day
  inTz x.tz do
    return (← mktime (.ofInt y) (.ofInt m) (.ofInt d) (.ofInt (x.sec / 3600)) (.ofInt (x.sec / 60 % 60))
      (.ofInt (x.sec % 60))).toInt

/-- Unix seconds e as (day, sec) on x's wall clock. -/
def frame (e : Int) (x : Dt) : IO (Int × Int) := do
  if x.kind == .utc then return (e / 86400, e % 86400)
  let t ← inTz x.tz (strftime "%Y %m %d %H %M %S" (.ofInt e))
  match (t.splitOn " ").filterMap String.toInt? with
  | [y, m, d, h, mi, s] => return (days y m d, h * 3600 + mi * 60 + s)
  | _ => throw <| IO.userError s!"localtime gave {t}"

/-- `(%d+)(%u)` matches of a duration's body, summed in seconds. -/
partial def unitSum (cs : List Char) (acc : Int) : Int :=
  match cs with
  | [] => acc
  | c :: r =>
    if c.isDigit then
      let rest := cs.dropWhile Char.isDigit
      match rest with
      | u :: r' =>
        if u.isUpper then
          let unit : Int := match u with
            | 'W' => 604800 | 'D' => 86400 | 'H' => 3600 | 'M' => 60 | 'S' => 1 | _ => 0
          unitSum r' (acc + ((digits (cs.takeWhile Char.isDigit)).getD 0) * unit)
        else unitSum rest acc
      | [] => acc
    else unitSum r acc

/-- RFC 5545 duration (no months in iCal) as seconds. -/
def duration (v : String) : Option Int :=
  let (neg, cs) := match v.toList with | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  match cs with
  | 'P' :: body@(_ :: _) => let n := unitSum (body.filter (· != 'T')) 0; some (if neg then -n else n)
  | _ => none

-- iCal text

partial def unescapeL (cs : List Char) (acc : Array Char) : Array Char :=
  match cs with
  | '\\' :: c :: r => unescapeL r (acc.push (if c == 'n' || c == 'N' then '\n' else c))
  | c :: r => unescapeL r (acc.push c)
  | [] => acc

def unescape (v : String) : String := String.ofList (unescapeL v.toList #[]).toList

def isNameChar (c : Char) : Bool := c.isAlphanum || c == '-'

/-- One content line: its name (upper case), parameters and value. -/
partial def contentline (line : String) : Option (String × Params × String) :=
  let cs := line.toList
  let name := cs.takeWhile isNameChar
  if name.isEmpty then none else
  let rec params (cs : List Char) (acc : Params) : Option (Params × List Char) :=
    match cs with
    | ';' :: r =>
      let k := r.takeWhile isNameChar
      match r.dropWhile isNameChar with
      | '=' :: v =>
        if k.isEmpty then none else
        let kv := fun (val : List Char) => (String.ofList k |>.toUpper, String.ofList val) :: acc
        match v with
        | '"' :: q =>
          match q.dropWhile (· != '"') with
          | '"' :: rest => params rest (kv (q.takeWhile (· != '"')))
          | _ => none
        | _ => params (v.dropWhile fun c => c != ';' && c != ':') (kv (v.takeWhile fun c => c != ';' && c != ':'))
      | _ => none
    | _ => some (acc, cs)
  match params (cs.drop name.length) [] with
  | some (ps, ':' :: value) => some ((String.ofList name).toUpper, ps, String.ofList value)
  | _ => none

structure PropV where
  value : String
  params : Params

/-- A VEVENT's or the calendar's own properties (not their VALARMs'), in order. -/
abbrev Comp := Array (String × PropV)

structure Cal where
  props : Comp := #[]
  events : Array Comp := #[]

def dropC (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)
def dropRightC (s : String) (n : Nat) : String := String.ofList (s.toList.take (s.length - n))

def parse (ics : String) : Cal := Id.run do
  let s := (ics.replace "\r\n" "\n").replace "\r" "\n"
  -- unfold: a line starting with a space or tab continues the one before (gsub("\n[ \t]", ""))
  let mut lines : Array String := #[]
  for l in s.splitOn "\n" do
    if (l.startsWith " " || l.startsWith "\t") && lines.size > 0 then
      lines := lines.modify (lines.size - 1) (· ++ dropC l 1)
    else lines := lines.push l
  let mut cal : Cal := {}
  let mut stack : Array String := #[]
  let mut ev : Option Comp := none
  for line in lines do
    if line.isEmpty then continue
    match contentline line with
    | some ("BEGIN", _, v) =>
      stack := stack.push v.toUpper
      if v.toUpper == "VEVENT" then ev := some #[]
    | some ("END", _, _) =>
      let top := stack.back?
      stack := stack.pop
      if top == some "VEVENT" then
        if let some e := ev then cal := { cal with events := cal.events.push e }
        ev := none
    | some (name, params, value) =>
      match stack.back? with
      | some "VEVENT" => ev := ev.map (·.push (name, { value, params }))
      | some "VCALENDAR" => cal := { cal with props := cal.props.push (name, { value, params }) }
      | _ => pure ()
    | none => pure ()
  return cal

def prop (ev : Comp) (name : String) : Option PropV := (ev.find? (·.1 == name)).map (·.2)
def props (ev : Comp) (name : String) : List PropV := (ev.toList.filter (·.1 == name)).map (·.2)
def text (ev : Comp) (name : String) : Option String := (prop ev name).map (unescape ·.value)
def textD (ev : Comp) (name d : String) : String := (text ev name).getD d
def propDt (ev : Comp) (name : String) : Option Dt := (prop ev name).bind fun p => valueDt p.value p.params

/-- Every value of a list property (EXDATE, RDATE). -/
def dts (ev : Comp) (name : String) : List Dt :=
  (props ev name).flatMap fun p => (commaPieces p.value).filterMap (valueDt · p.params)

-- Recurrence

def WD : List (String × Int) := [("SU", 0), ("MO", 1), ("TU", 2), ("WE", 3), ("TH", 4), ("FR", 5), ("SA", 6)]
def wdOf (s : String) : Option Int := (WD.find? (·.1 == s)).map (·.2)
def PARTS : List String := ["FREQ", "INTERVAL", "COUNT", "UNTIL", "BYDAY", "BYMONTHDAY", "BYMONTH", "BYSETPOS", "WKST"]
def FREQS : List String := ["DAILY", "WEEKLY", "MONTHLY", "YEARLY"]

/-- gmatch("([^<sep>=]+)=([^<sep>]*)"): the key=value pairs of `s`. -/
def kvPairs (s : String) (sep : Char) : List (String × String) :=
  (s.splitOn (String.singleton sep)).filterMap fun piece =>
    let cs := piece.toList.dropWhile (· == '=')
    match cs.dropWhile (· != '=') with
    | '=' :: v => some (String.ofList (cs.takeWhile (· != '=')), String.ofList v)
    | _ => none

structure WdSpec where
  n : Option Int
  wd : Int

structure Rule where
  freq : String
  interval : Int
  count : Option Int
  wkst : Int
  months : Option (List Int)
  mdays : Option (List Int)
  setpos : Option (List Int)
  wdays : Option (List WdSpec) := none
  «until» : Option Dt := none

def nums (v : Option String) : Option (List Int) := v.map fun v => (commaPieces v).filterMap parseInt

/-- gmatch("([+-]?%d*)(%u%u)"). -/
partial def bydays (cs : List Char) (acc : Array (String × String)) : Array (String × String) :=
  match cs with
  | [] => acc
  | c :: r =>
    let afterSign := if c == '+' || c == '-' then r else cs
    let rest := afterSign.dropWhile Char.isDigit
    match rest with
    | a :: b :: r' =>
      if a.isUpper && b.isUpper then
        bydays r' (acc.push (String.ofList (cs.take (cs.length - rest.length)), String.ofList [a, b]))
      else bydays r acc
    | _ => bydays r acc

/-- RRULE value → rule, or the part it can't expand. -/
def rule (s : String) : Except String Rule := do
  let pairs := (kvPairs s ';').map fun (k, v) => (k.toUpper, v)
  let r (k : String) : Option String := (pairs.reverse.find? (·.1 == k)).map (·.2)
  if let some (k, _) := pairs.find? (!PARTS.contains ·.1) then throw k
  let freq := (r "FREQ").getD "nil"
  if !FREQS.contains freq then throw s!"FREQ={freq}"
  let interval := ((r "INTERVAL").bind parseInt).getD 1
  let count := (r "COUNT").bind parseInt
  let wkst := (wdOf ((r "WKST").getD "MO")).getD 1
  let mut o : Rule := Rule.mk freq interval count wkst (nums (r "BYMONTH")) (nums (r "BYMONTHDAY")) (nums (r "BYSETPOS")) none none
  if let some bd := r "BYDAY" then
    let mut ws := #[]
    for (n, w) in bydays bd.toList #[] do
      let some wd := wdOf w | throw s!"BYDAY={bd}"
      ws := ws.push { n := parseInt n, wd }
    o := { o with wdays := some ws.toList }
  if o.freq == "YEARLY" && o.wdays.isSome && o.months.isNone then throw "YEARLY BYDAY without BYMONTH"
  if let some u := r "UNTIL" then o := { o with «until» := valueDt u [] }
  return o

def pick (l : List Int) (i : Int) : Option Int := -- Lua's l[i > 0 and i or #l + 1 + i]
  let j := if i > 0 then i else l.length + 1 + i
  if 1 ≤ j && j ≤ l.length then l[(j - 1).toNat]? else none

/-- The days a MONTHLY/YEARLY rule picks in month m of year y. -/
def monthDays (o : Rule) (y m d0 : Int) : List Int :=
  let n := dim y m
  let first := days y m 1
  let byM : List Int := (o.mdays.getD []).filterMap fun md =>
    let d := if md < 0 then n + 1 + md else md
    if 1 ≤ d && d ≤ n then some (first + d - 1) else none
  let set := match o.wdays with
    | some ws =>
      let w := ws.flatMap fun e =>
        let hits := ((List.range n.toNat).map fun i => first + Int.ofNat i).filter (wday · == e.wd)
        match e.n with
        | some k => (pick hits k).toList
        | none => hits
      if o.mdays.isSome then byM.filter w.contains else w
    | none => byM
  if o.mdays.isNone && o.wdays.isNone && d0 ≤ n then set ++ [first + d0 - 1] else set

def sortSet (l : List Int) : List Int := l.eraseDups.mergeSort (· ≤ ·)

/-- The k-th period's candidate days (sorted) and the day it starts on. -/
def period (o : Rule) (s k : Int) : List Int × Int :=
  let (y0, m0, d0) := civil s
  let (set, start) : List Int × Int := match o.freq with
    | "DAILY" => let st := s + k * o.interval; ([st], st)
    | "WEEKLY" =>
      let st := s - (wday s - o.wkst) % 7 + 7 * o.interval * k
      ((o.wdays.getD [{ n := none, wd := wday s }]).map fun e => st + (e.wd - o.wkst) % 7, st)
    | "MONTHLY" =>
      let i := y0 * 12 + m0 - 1 + k * o.interval
      let (y, m) := (i / 12, i % 12 + 1)
      (monthDays o y m d0, days y m 1)
    | _ =>
      let y := y0 + k * o.interval
      ((o.months.getD [m0]).flatMap (monthDays o y · d0), days y 1 1)
  let out := sortSet <| set.filter fun z =>
    let (y, m, d) := civil z
    o.months.all (·.contains m) &&
    (o.freq != "DAILY" || o.wdays.all (·.any (·.wd == wday z))) &&
    (o.freq != "DAILY" || o.mdays.all (·.any fun md => (if md < 0 then dim y m + 1 + md else md) == d))
  match o.setpos with
  | some ps => (sortSet (ps.filterMap (pick out ·)), start)
  | none => (out, start)

/-- The days in [lo, hi] the series starting at s occurs on, in s's frame, honoring COUNT and UNTIL.
DTSTART is always one, even off the rule (then outside COUNT), as dateutil and Google do. -/
def occurrences (o : Rule) (s : Dt) (lo hi : Int) : IO (List Int) := do
  let huge : Int := 1000000 -- past any second of a day: math.huge
  let (ud, us) ← match o.«until» with -- UNTIL on s's wall clock
    | none => pure (none, 0)
    | some u =>
      if u.kind == .date || s.kind == .date then pure (some u.day, huge)
      else if u.kind == .utc then do let (d, sec) ← frame (← epoch u) s; pure (some d, sec)
      else pure (some u.day, u.sec)
  let mut out : Array Int := if s.day ≥ lo && s.day ≤ hi then #[s.day] else #[]
  let mut n := 0
  for k in [0:1000001] do
    let (cand, start) := period o s.day k
    if start > hi then break
    for z in cand do
      if z ≥ s.day then
        if let some ud := ud then
          if z > ud || (z == ud && s.sec > us) then return out.toList
        n := n + 1
        if o.count.any (n > ·) || z > hi then return out.toList
        if z ≥ lo && z != s.day then out := out.push z
  return out.toList

-- HTML in descriptions

/-- utf8.char(n) for 0 < n < 0x110000.
shortcut: a surrogate (which lua-utf8 writes as bytes no UTF-8 reader takes) keeps its entity; fine for invites. -/
def cp (n : Nat) : Option Char := if 0 < n && n < 0x110000 && (n < 0xD800 || n > 0xDFFF) then some (Char.ofNat n) else none

def LATIN1 : List String := ("nbsp iexcl cent pound curren yen brvbar sect uml copy ordf laquo not shy reg macr deg plusmn " ++
  "sup2 sup3 acute micro para middot cedil sup1 ordm raquo frac14 frac12 frac34 iquest Agrave Aacute Acirc Atilde Auml " ++
  "Aring AElig Ccedil Egrave Eacute Ecirc Euml Igrave Iacute Icirc Iuml ETH Ntilde Ograve Oacute Ocirc Otilde Ouml times " ++
  "Oslash Ugrave Uacute Ucirc Uuml Yacute THORN szlig agrave aacute acirc atilde auml aring aelig ccedil egrave eacute " ++
  "ecirc euml igrave iacute icirc iuml eth ntilde ograve oacute ocirc otilde ouml divide oslash ugrave uacute ucirc uuml " ++
  "yacute thorn yuml").splitOn " "

/-- HTML's Latin-1 entities (U+00A0..U+00FF in order) plus the punctuation calendar invites use. -/
def ENT : List (String × Char) :=
  [("amp", '&'), ("lt", '<'), ("gt", '>'), ("quot", '"'), ("apos", '\''), ("rsquo", '’'), ("lsquo", '‘'), ("rdquo", '”'),
   ("ldquo", '“'), ("sbquo", '‚'), ("bdquo", '„'), ("ndash", '–'), ("mdash", '—'), ("hellip", '…'), ("bull", '•'),
   ("trade", '™'), ("euro", '€'), ("dagger", '†'), ("ensp", ' '), ("emsp", ' '), ("thinsp", ' '),
   ("zwnj", '‌'), ("zwj", '‍'), ("lrm", '‎'), ("rlm", '‏')] ++
  LATIN1.zipIdx.map fun (n, i) => (n, Char.ofNat (0xA0 + i))

/-- gsub with a matcher: at each position `f` gives the replacement and the rest after the match, else the
character stays. -/
partial def gsubL (f : List Char → Option (List Char × List Char)) (cs : List Char) (acc : Array Char) : Array Char :=
  match cs with
  | [] => acc
  | c :: r =>
    match f cs with
    | some (rep, rest) => gsubL f rest (acc ++ rep.toArray)
    | none => gsubL f r (acc.push c)

def gsub (f : List Char → Option (List Char × List Char)) (s : String) : String :=
  String.ofList (gsubL f s.toList #[]).toList

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10) else none

def hexNum (cs : List Char) : Nat := cs.foldl (fun n c => n * 16 + (hexVal c).getD 0) 0

/-- `<prefix>(run of chars)<;>` with the run's text replaced by `f`, the match kept when `f` gives none. -/
def entityRun (pre : List Char) (ok : Char → Bool) (f : List Char → Option Char) (cs : List Char) :
    Option (List Char × List Char) :=
  if !pre.isPrefixOf cs then none else
  let r := cs.drop pre.length
  let run := r.takeWhile ok
  match r.drop run.length with
  | ';' :: rest => if run.isEmpty then none else
      some ((f run).map ([·]) |>.getD (cs.take (pre.length + run.length + 1)), rest)
  | _ => none

def unhtml (s : String) : String :=
  let s := gsub (fun cs => match cs with
    | '&' :: '#' :: x :: _ => if x == 'x' || x == 'X' then entityRun ['&', '#', x] (hexVal · |>.isSome) (cp ∘ hexNum) cs else none
    | _ => none) s
  let s := gsub (entityRun ['&', '#'] Char.isDigit fun ds => cp (String.ofList ds).toNat!) s
  gsub (entityRun ['&'] Char.isAlpha fun n => (ENT.find? (·.1 == String.ofList n)).map (·.2)) s

def isWs (c : Char) : Bool := isSpace c || c == ' '
def rstrip (s : String) : String := String.ofList (s.toList.reverse.dropWhile isWs).reverse
def stripN (s : String) : String := rstrip (String.ofList (s.toList.dropWhile isWs))

/-- The index of the first `pat` in `cs` at or after `i`. -/
partial def findFrom (cs pat : List Char) (i : Nat := 0) : Option Nat :=
  match cs with
  | [] => if pat.isEmpty then some i else none
  | _ :: r => if pat.isPrefixOf cs then some i else findFrom r pat (i + 1)

def hasSubL (s sub : String) : Bool := (findFrom s.toList sub.toList).isSome

/-- Google's conference block and its "Join with Google Meet" tail. -/
def dropJoin (s : String) : String :=
  let a := "-::~:~::~".toList
  let b := "::~:~::-".toList
  -- gsub("%-::~:~::~.-::~:~::%-", ""): once no end follows a start, no later start has one either
  let rec go (cs : List Char) (acc : Array Char) (fuel : Nat) : Array Char :=
    match fuel, findFrom cs a with
    | fuel + 1, some i =>
      let after := cs.drop (i + a.length)
      match findFrom after b with
      | some j => go (after.drop (j + b.length)) (acc ++ (cs.take i).toArray) fuel
      | none => acc ++ cs.toArray
    | _, _ => acc ++ cs.toArray
  let cs := (go s.toList #[] s.length).toList
  match findFrom cs "Join with Google Meet:".toList with
  | some j => String.ofList ((cs.take j).reverse.dropWhile (· == '\n')).reverse
  | none => String.ofList cs

/-- `+` as a space and `%XX` as its byte (Python's unquote_plus). -/
def unquotePlus (s : String) : String := Id.run do
  let b := s.toUTF8
  let mut out : ByteArray := .empty
  let mut i := 0
  while i < b.size do
    let c := b[i]!
    if c == 43 then out := out.push 32; i := i + 1
    else if c == 37 && i + 2 < b.size then
      match hexVal (Char.ofNat b[i+1]!.toNat), hexVal (Char.ofNat b[i+2]!.toNat) with
      | some h, some l => out := out.push (h * 16 + l).toUInt8; i := i + 3
      | _, _ => out := out.push c; i := i + 1
    else out := out.push c; i := i + 1
  -- shortcut: bytes that aren't UTF-8 read as Latin-1, where Lua passed them through; a bad link title at worst
  return (String.fromUTF8? out).getD (String.ofList (out.toList.map (Char.ofNat ·.toNat)))

/-- A URL's host, path and query. -/
def urlparts (u : String) : String × String × String :=
  let cs := u.toList
  let pathQuery (rest : List Char) : String × String :=
    let path := rest.takeWhile fun c => c != '?' && c != '#'
    let q := match rest.dropWhile (· != '?') with | _ :: r => r.takeWhile (· != '#') | [] => []
    (String.ofList path, String.ofList q)
  let scheme := match cs with
    | c :: r => if c.isAlpha then
        match r.dropWhile fun (c : Char) => c.isAlphanum || c == '+' || c == '.' || c == '-' with
        | ':' :: '/' :: '/' :: rest => some rest
        | _ => none
      else none
    | [] => none
  match scheme with
  | some rest =>
    let host := rest.takeWhile fun c => c != '/' && c != '?' && c != '#'
    let (p, q) := pathQuery (rest.drop host.length)
    (String.ofList host, p, q)
  | none => let (p, q) := pathQuery cs; ("", p, q)

def DOCS : List (String × String) :=
  [("document", "Google Doc"), ("spreadsheets", "Google Sheet"), ("presentation", "Google Slides"), ("forms", "Google Form")]

def has3Alpha (s : String) : Bool :=
  let rec go : List Char → Bool
    | a :: b :: c :: r => (a.isAlpha && b.isAlpha && c.isAlpha) || go (b :: c :: r)
    | _ => false
  go s.toList

/-- A readable name for a link: Google file type, else the last wordy path segment (Confluence titles), else the host. -/
def pretty (url : String) : String :=
  let (host, path, _) := urlparts url
  if host == "docs.google.com" then
    let first := match path.toList with | '/' :: r => String.ofList (r.takeWhile (· != '/')) | _ => ""
    ((DOCS.find? (·.1 == first)).map (·.2)).getD "Google file"
  else
    let p := if path.endsWith "/overview/" then dropRightC path 1 else path
    let space := if p.endsWith "/overview" then
        let q := dropRightC p 9
        let seg := (q.splitOn "/").getLastD ""
        if seg != "" && q.endsWith ("/spaces/" ++ seg) then some seg else none
      else none
    match space with
    | some sp => sp ++ " space"
    | none =>
      match ((path.splitOn "/").filter fun s => s != "" && has3Alpha s).getLast? with
      | some seg => unquotePlus seg
      | none => host

/-- Google's /url?q= redirect → its target. -/
def unwrap (url : String) : String :=
  let (host, path, query) := urlparts url
  if host.endsWith "google.com" && path == "/url" then
    match (kvPairs query '&').find? fun (k, v) => unquotePlus k == "q" && v != "" with
    | some (_, v) => unquotePlus v
    | none => url
  else url

-- Links and attachments come from the invite's author, and the panel opens them: web addresses only.
def web (url : String) : Bool := let l := url.toLower; l.startsWith "http://" || l.startsWith "https://"

/-- gsub("<[^>]+>", with). -/
def tags (s : String) (with_ : String) : String :=
  gsub (fun cs => match cs with
    | '<' :: c :: r => if c == '>' then none else
        match (c :: r).dropWhile (· != '>') with
        | '>' :: rest => some (with_.toList, rest)
        | _ => none
    | _ => none) s

def lowerEq (c : Char) (l : Char) : Bool := c.toLower == l

/-- (.-)</[aA]>: the text before the first `</a>` and the rest after it. -/
partial def closeA (cs : List Char) (acc : Array Char := #[]) : Option (List Char × List Char) :=
  match cs with
  | '<' :: r => match r with
    | '/' :: a :: '>' :: rest => if lowerEq a 'a' then some (acc.toList, rest) else closeA r (acc.push '<')
    | _ => closeA r (acc.push '<')
  | c :: r => closeA r (acc.push c)
  | [] => none

/-- `<[aA]%s[^>]-[hH][rR][eE][fF]="([^"]+)"[^>]*>(.-)</[aA]>` at the start of cs: url, text, rest. -/
def anchorAt (cs : List Char) : Option (String × String × List Char) :=
  let href (cs : List Char) : Option (String × String × List Char) :=
    match cs with
    | h :: r :: e :: f :: '=' :: '"' :: rest =>
      if !(lowerEq h 'h' && lowerEq r 'r' && lowerEq e 'e' && lowerEq f 'f') then none else
      let url := rest.takeWhile (· != '"')
      match rest.drop url.length with
      | '"' :: r2 =>
        if url.isEmpty then none else
        match r2.dropWhile (· != '>') with
        | '>' :: r3 => (closeA r3).map fun (t, rest) => (String.ofList url, String.ofList t, rest)
        | _ => none
      | _ => none
    | _ => none
  let rec lazy (cs : List Char) : Option (String × String × List Char) := -- [^>]-
    match href cs with
    | some x => some x
    | none => match cs with
      | c :: r => if c == '>' then none else lazy r
      | [] => none
  match cs with
  | '<' :: a :: sp :: r => if lowerEq a 'a' && isSpace sp then lazy r else none
  | _ => none

partial def anchors (cs : List Char) (acc : Array (String × String)) : Array (String × String) :=
  match cs with
  | [] => acc
  | _ :: r => match anchorAt cs with
    | some (u, t, rest) => anchors rest (acc.push (u, t))
    | none => anchors r acc

/-- gmatch('https?://[^%s<>"]+'). -/
partial def httpUrls (cs : List Char) (acc : Array String) : Array String :=
  let ok (c : Char) := !(isSpace c || c == '<' || c == '>' || c == '"')
  let after : Option (List Char) := match cs with
    | 'h' :: 't' :: 't' :: 'p' :: ':' :: '/' :: '/' :: r => some r
    | 'h' :: 't' :: 't' :: 'p' :: 's' :: ':' :: '/' :: '/' :: r => some r
    | _ => none
  match cs, after with
  | [], _ => acc
  | _ :: r, none => httpUrls r acc
  | _ :: r, some a =>
    let body := a.takeWhile ok
    if body.isEmpty then httpUrls r acc
    else httpUrls (a.drop body.length) (acc.push (String.ofList (cs.take (cs.length - a.length) ++ body)))

def SKIP : List String := ["meet.google.com", "tel.meet", "zoom.us/j", "support.google.com"]

def links (raw : String) : List Json := Id.run do
  let raw := dropJoin raw
  let mut order : Array (String × String) := #[]
  let add (o : Array (String × String)) (u t : String) := if o.any (·.1 == u) then o else o.push (u, t)
  for (u, t) in anchors raw.toList #[] do
    let u := unwrap (unhtml u)
    if web u then order := add order u (stripN (unhtml (tags t "")))
  for u in httpUrls (unhtml (tags raw " ")).toList #[] do
    let u := String.ofList (u.toList.takeWhile (· != ' '))
    order := add order (unwrap (String.ofList (u.toList.reverse.dropWhile (fun c => c == '.' || c == ',' || c == ')')).reverse)) ""
  return order.toList.filterMap fun (u, t) =>
    if SKIP.any (hasSubL u ·) then none
    else some (Json.mkObj [("title", if t != "" && t != u then t else pretty u), ("url", u), ("host", (urlparts u).1)])

/-- A tag matcher: `<`, then `name` (any case), then `tail` accepted on the rest. -/
def tagAt (name : String) (tail : List Char → Option (List Char)) (cs : List Char) : Option (List Char × List Char) :=
  match cs with
  | '<' :: r =>
    let n := name.toList
    if r.length < n.length || !(r.take n.length |>.zip n |>.all fun (c, l) => lowerEq c l) then none
    else (tail (r.drop n.length)).map (['\n'], ·)
  | _ => none

def plain (s : String) (drop : List String) : String := Id.run do
  let mut s := dropJoin s
  s := gsub (tagAt "br" fun r => match (r.dropWhile isSpace) with
    | '/' :: '>' :: rest => some rest | '>' :: rest => some rest | _ => none) s
  s := gsub (tagAt "/p" fun r => match r with | '>' :: rest => some rest | _ => none) s
  s := gsub (tagAt "/li" fun r => match r with | '>' :: rest => some rest | _ => none) s
  s := unhtml (tags s "")
  for u in drop do if u != "" then s := s.replace u ""
  -- the line breaks Python's str.splitlines knows, as \n
  s := s.replace "\r\n" "\n"
  s := String.map (fun c => if c == '\r' || c == '\x0b' || c == '\x0c' || c == '\x1c' || c == '\x1d' || c == '\x1e' ||
    c == '\u0085' || c == ' ' || c == ' ' then '\n' else c) s
  s := "\n".intercalate ((s.splitOn "\n").map rstrip)
  -- gsub("\n\n\n+", "\n\n")
  let mut out : Array Char := #[]
  let mut run := 0
  for c in s.toList do
    if c == '\n' then run := run + 1 else run := 0
    if c != '\n' || run ≤ 2 then out := out.push c
  return cut (stripN (String.ofList out.toList)) 3000

/-- The earliest i ≥ 0 where `m` matches cs.drop i, with the match's length. -/
partial def findMatch (m : List Char → Option Nat) (cs : List Char) (i : Nat := 0) : Option (Nat × Nat) :=
  match m cs, cs with
  | some n, _ => some (i, n)
  | none, [] => none
  | none, _ :: r => findMatch m r (i + 1)

/-- The meeting's Meet or Zoom link. -/
def firstLink (s : String) : Option String :=
  let cs := s.toList
  let meetP := "https://meet.google.com/".toList
  let meet (cs : List Char) : Option Nat :=
    if !meetP.isPrefixOf cs then none else
    let n := ((cs.drop meetP.length).takeWhile fun c => ('a' ≤ c && c ≤ 'z') || c == '-').length
    if n == 0 then none else some (meetP.length + n)
  let zoom (cs : List Char) : Option Nat :=
    if !"https://".toList.isPrefixOf cs then none else
    let r := cs.drop 8
    let host := r.takeWhile fun c => c.isAlphanum || c == '_' || c == '.' || c == '-'
    let j := "/j/".toList
    if !(String.ofList host).endsWith "zoom.us" || !j.isPrefixOf (r.drop host.length) then none else
    let n := ((r.drop (host.length + 3)).takeWhile fun c => !(isSpace c || c == '"' || c == '<' || c == '>' || c == '\\')).length
    if n == 0 then none else some (8 + host.length + 3 + n)
  let get (x : Nat × Nat) := String.ofList ((cs.drop x.1).take x.2)
  match findMatch meet cs, findMatch zoom cs with
  | some a, some b => some (get (if a.1 ≤ b.1 then a else b))
  | some a, none => some (get a)
  | none, some b => some (get b)
  | none, none => none

def files (ev : Comp) : List Json :=
  (props ev "ATTACH").filterMap fun a =>
    let url := a.value
    let fmt := (param a.params "FMTTYPE").getD ""
    let kind := if fmt.startsWith "video/" then "recording"
      else if hasSubL fmt "google-apps" || hasSubL url "docs.google.com" then "doc" else "file"
    if web url then some (Json.mkObj [("title", (param a.params "FILENAME").getD (pretty url)), ("url", url), ("kind", kind)])
    else none

def B64 : Array Char := "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_".toList.toArray

/-- URL-safe base64, unpadded. -/
def b64url (s : String) : String := Id.run do
  let b := s.toUTF8
  let mut out : Array Char := #[]
  let mut i := 0
  while i < b.size do
    let get (k : Nat) := if i + k < b.size then b[i + k]!.toNat else 0
    let n := get 0 * 65536 + get 1 * 256 + get 2
    let k := if i + 1 ≥ b.size then 2 else if i + 2 ≥ b.size then 3 else 4
    for j in [1:k+1] do out := out.push B64[(n / 64 ^ (4 - j)) % 64]!
    i := i + 3
  return String.ofList out.toList

/-- Google's event id: the UID's prefix, plus _<original start> for one instance of a recurring event. -/
def googleId (ev : Comp) (occ : Dt) (recurring : Bool) : IO (Option String) := do
  let uid := textD ev "UID" ""
  if !uid.endsWith "@google.com" then return none
  let base := dropRightC uid 11
  -- a split series' UID carries _R<series start>
  let tail := (base.toList.reverse.take 17).reverse
  let base := match tail with
    | '_' :: 'R' :: r => if r.length == 15 && r[8]! == 'T' && (r.take 8 ++ r.drop 9).all Char.isDigit then
        dropRightC base 17 else base
    | _ => base
  if !recurring then return some base
  let x := (propDt ev "RECURRENCE-ID").getD occ
  if x.kind == .date then return some s!"{base}_{ymd x.day ""}"
  let e ← epoch x
  return some s!"{base}_{ymd (e / 86400) ""}T{hhmmss (e % 86400)}Z"

/-- One record of the panel; also what its sort needs. -/
structure Rec where
  day : String := ""
  allDay : Bool
  start : Option Int
  title : String
  id : Option String
  fields : List (String × Json)

def jstr : Option String → Json | some s => .str s | none => .null
def jint : Option Int → Json | some i => Json.int i | none => .null

/-- The panel's record for one occurrence; none when cancelled or declined. -/
def record (ev : Comp) (x : Dt) (st en : Option Int) (recurring : Bool) (me calendarId : String)
    (internal : Option (List String)) : IO (Option Rec) := do
  let attendees := props ev "ATTENDEE"
  let mut mine := (attendees.find? (·.value.toLower == me)).bind (param ·.params "PARTSTAT")
  if text ev "STATUS" == some "CANCELLED" || mine == some "DECLINED" then return none
  let org := prop ev "ORGANIZER"
  if org.any (·.value.toLower == me) then mine := some "ACCEPTED"
  let attached := files ev
  let seen := attached.filterMap (·.getObjValAs? String "url" |>.toOption)
  let found := (links (textD ev "DESCRIPTION" "")).filter fun l =>
    !seen.contains ((l.getObjValAs? String "url").toOption.getD "")
  let drop := found.filterMap (·.getObjValAs? String "url" |>.toOption)
  let people := (attendees.take 60).map fun a =>
    let email := dropC a.value 7
    let domain := match email.toList.dropWhile (· != '@') with | _ :: r => String.ofList r | [] => ""
    Json.mkObj [("name", (param a.params "CN").getD email), ("email", email),
      ("status", (param a.params "PARTSTAT").getD "NEEDS-ACTION"),
      ("external", internal.any fun i => email != "" && !i.contains domain.toLower)]
  let gid ← googleId ev x recurring
  let link := firstLink s!"{textD ev "X-GOOGLE-CONFERENCE" ""} {textD ev "LOCATION" ""} {textD ev "DESCRIPTION" ""}"
  let title := textD ev "SUMMARY" "(no title)"
  return some { allDay := st.isNone, start := st.map (· * 1000), title, id := gid, fields := [
    ("title", .str title), ("all_day", .bool st.isNone), ("start", jint (st.map (· * 1000))),
    ("end", jint (en.map (· * 1000))), ("link", jstr link), ("id", jstr gid),
    ("open", jstr (gid.map fun g => "https://www.google.com/calendar/event?eid=" ++ b64url (g ++ " " ++ calendarId))),
    ("rsvp", .str (mine.getD "ACCEPTED")), ("location", .str (textD ev "LOCATION" "")),
    ("description", .str (plain (textD ev "DESCRIPTION" "") drop)), ("links", .arr found.toArray),
    ("files", .arr attached.toArray),
    ("organizer", jstr (org.map fun o => (param o.params "CN").getD (dropC o.value 7))),
    ("organizer_email", jstr (org.map (dropC ·.value 7))), ("attendees", .arr people.toArray)] }

def Rec.json (r : Rec) : Json := Json.mkObj (("day", .str r.day) :: r.fields)

/-- LuaJIT's %q. -/
def luaQ (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c => match c with
    | '"' => "\\\"" | '\\' => "\\\\" | '\n' => "\\\n" | '\r' => "\\13" | '\x00' => "\\0" | c => c.toString) ++ "\""

/-- Events overlapping local days [today, today + 2), one record under each day it overlaps (`day`), sorted by day,
all-day first, then start. -/
def events (cal : Cal) (today : Int) (internal : Option (List String)) : IO (List Rec) := do
  let calendarId := textD cal.props "X-WR-CALNAME" ""
  let me := ("mailto:" ++ calendarId).toLower
  let localMidnight : Dt := { day := 0, kind := .float }
  let key (x : Dt) : IO String := if x.kind == .date then pure s!"d{x.day}" else return toString (← epoch x)
  let mut moved : Std.HashMap String (Array String) := {} -- uid → instances an override replaces
  for ev in cal.events do
    if let some r := propDt ev "RECURRENCE-ID" then
      let uid := textD ev "UID" ""
      moved := moved.insert uid ((moved.getD uid #[]).push (← key r))
  let mut out : Array Rec := #[]
  for ev in cal.events do
    let some s := propDt ev "DTSTART" | continue
    let e := propDt ev "DTEND"
    let d := (prop ev "DURATION").bind (duration ·.value)
    let len ← if s.kind == .date then pure (max (match e with | some e => e.day - s.day | none => d.getD 86400 / 86400) 1)
      else match e with | some e => (do pure ((← epoch e) - (← epoch s))) | none => pure (d.getD 0)
    let rr := prop ev "RRULE"
    let override := (prop ev "RECURRENCE-ID").isSome
    let mut starts : Array Dt := #[s]
    if let some rr := rr then
      if !override then
        starts := #[]
        match rule rr.value with
        | .error why => warn s!"skipped {luaQ (textD ev "SUMMARY" "?")}: can't expand its RRULE {why}"
        | .ok o =>
          let uid := textD ev "UID" ""
          let mut skip := moved.getD uid #[]
          for x in dts ev "EXDATE" do skip := skip.push (← key x)
          -- Lua adds EXDATEs into the uid's moved set itself, so a later VEVENT of the same UID skips them too
          if moved.contains uid then moved := moved.insert uid skip
          let back := if s.kind == .date then len else -((-len) / 86400)
          for z in ← occurrences o s (today - 2 - back) (today + 3) do
            let x := { s with day := z }
            if !skip.contains (← key x) then starts := starts.push x
          for x in dts ev "RDATE" do
            if !skip.contains (← key x) then starts := starts.push x
    for x in starts do
      let st ← if x.kind != .date then some <$> epoch x else pure none
      let en := st.map (· + len)
      for dd in [0:2] do
        let d := today + Int.ofNat dd
        let keep ← match st, en with
          | some st, some en => do
            let ds ← epoch localMidnight (some d); let de ← epoch localMidnight (some (d + 1))
            pure (st < de && (en > ds || st ≥ ds))
          | _, _ => pure (x.day ≤ d && x.day + len > d)
        if keep then
          if let some r ← record ev x st en (rr.isSome || override) me calendarId internal then
            out := out.push { r with day := ymd d }
  let lt (a b : Rec) : Bool :=
    if a.day != b.day then a.day < b.day
    else if a.allDay != b.allDay then a.allDay
    else if !a.allDay && a.start != b.start then a.start.getD 0 < b.start.getD 0
    else a.title ++ a.id.getD "userdata: NULL" < b.title ++ b.id.getD "userdata: NULL"
  return out.toList.mergeSort fun a b => !lt b a

def selftest : IO UInt32 := do
  origTz.set (some "America/New_York")
  let ics := "BEGIN:VCALENDAR
X-WR-CALNAME:me@example.com
BEGIN:VEVENT
UID:a_R20260616T151000@google.com
SUMMARY:Standup
DTSTART:20261102T150000Z
DTEND:20261102T151500Z
RRULE:FREQ=DAILY
LOCATION:https://meet.google.com/abc-defg-hij
BEGIN:VALARM
DESCRIPTION:This is an event reminder
END:VALARM
END:VEVENT
BEGIN:VEVENT
UID:t
SUMMARY:Maybe
DTSTART:20261103T190000Z
DTEND:20261103T193000Z
DESCRIPTION:Agenda<br>item <a href=\"file:///Applications/Calculator.app\">agenda</a> <a href=\"https://x.atlassian.net/wiki/pages/1/Retro+Notes\">https://x.atlassian.net/wiki/pages/1/Retro+Notes</a> -::~:~::~join here::~:~::-\\n\\nJoin with Google Meet: https://meet.google.com/x\\nOr dial: 1
ATTACH;FILENAME=\"Notes - 1:1\";FMTTYPE=application/vnd.google-apps.document:https://docs.google.com/document/d/abc/edit
ATTACH;FILENAME=\"Recording\";FMTTYPE=video/mp4:https://drive.google.com/file/d/def/view
ATTACH;FILENAME=\"Share\":smb://host/share
ATTENDEE;CN=Me;PARTSTAT=TENTATIVE:mailto:me@example.com
ATTENDEE;PARTSTAT=ACCEPTED:mailto:guest@other.org
END:VEVENT
BEGIN:VEVENT
UID:b
SUMMARY:Declined
DTSTART:20261103T170000Z
DTEND:20261103T180000Z
ATTENDEE;PARTSTAT=DECLINED:mailto:me@example.com
END:VEVENT
BEGIN:VEVENT
UID:c
SUMMARY:Offsite
DTSTART;VALUE=DATE:20261104
DTEND;VALUE=DATE:20261105
END:VEVENT
END:VCALENDAR"
  let got := (← events (parse (ics.replace "\n" "\r\n")) (days 2026 11 3) (some ["example.com"])).toArray.map Rec.json
  let eq (a b : Json) (what : String) : IO Unit := do
    unless a == b do throw <| IO.userError s!"{what}: got {a.compress}, want {b.compress}"
  let strs (l : List String) : Json := .arr (l.map Json.str).toArray
  let g (i : Nat) (k : String) : Json := got[i]!.getObjValD k
  eq (.arr (got.map (·.getObjValD "title"))) (strs ["Standup", "Maybe", "Offsite", "Standup"]) "titles"
  eq (.arr #[g 1 "rsvp", g 1 "description"]) (strs ["TENTATIVE", "Agenda\nitem agenda"]) "rsvp, description" -- the file:// link's text stays, its address goes
  eq (.str (plain "a \nb\r\nc" [])) (.str "a\n\nb\nc") "line separators"
  eq (g 1 "attendees") (.arr #[
    Json.mkObj [("name", "Me"), ("email", "me@example.com"), ("status", "TENTATIVE"), ("external", false)],
    Json.mkObj [("name", "guest@other.org"), ("email", "guest@other.org"), ("status", "ACCEPTED"), ("external", true)]])
    "attendees"
  eq (.arr #[g 0 "organizer_email", g 0 "rsvp", g 0 "links", g 0 "files", g 0 "description"])
    (.arr #[.null, "ACCEPTED", .arr #[], .arr #[], ""]) "standup"
  eq (g 1 "links") (.arr #[Json.mkObj [("title", "Retro Notes"), ("url", "https://x.atlassian.net/wiki/pages/1/Retro+Notes"),
    ("host", "x.atlassian.net")]]) "links"
  let file (i : Nat) (k : String) : Json := (match g 1 "files" with | .arr a => a[i]!.getObjValD k | _ => .null)
  eq (.arr #[file 0 "title", file 0 "kind", file 1 "title", file 1 "kind"]) (strs ["Notes - 1:1", "doc", "Recording", "recording"]) "files"
  eq (.arr #[g 0 "id", g 3 "id", g 1 "id"]) (.arr #["a_20261103T150000Z", "a_20261104T150000Z", .null]) "ids"
  eq (.arr #[g 0 "link", g 2 "all_day", g 2 "day"]) (.arr #["https://meet.google.com/abc-defg-hij", true, "2026-11-04"]) "link, all-day"
  eq (g 0 "open") (.str ("https://www.google.com/calendar/event?eid=" ++ b64url "a_20261103T150000Z me@example.com")) "open"

  -- Rules: window is Tue 2026-11-03 and Wed 2026-11-04, New York.
  let ev (uid summary lines : String) := s!"BEGIN:VEVENT\nUID:{uid}\nSUMMARY:{summary}\n{lines}\nEND:VEVENT\n"
  let got ← events (parse ("BEGIN:VCALENDAR\n"
    ++ ev "tz" "Tue Thu NY" "DTSTART;TZID=America/New_York:20260303T090000\nDTEND;TZID=America/New_York:20260303T093000\nRRULE:FREQ=WEEKLY;BYDAY=TU,TH"
    ++ ev "first-tue" "First Tuesday" "DTSTART:20260106T170000Z\nDTEND:20260106T180000Z\nRRULE:FREQ=MONTHLY;BYDAY=1TU"
    ++ ev "last-day" "Last day" "DTSTART;VALUE=DATE:20260131\nRRULE:FREQ=MONTHLY;BYMONTHDAY=-1"
    ++ ev "biweekly" "Every other Wed" "DTSTART:20261021T160000Z\nDTEND:20261021T163000Z\nRRULE:FREQ=WEEKLY;INTERVAL=2;BYDAY=WE"
    ++ ev "off-week" "Other other Wed" "DTSTART:20261028T160000Z\nDTEND:20261028T163000Z\nRRULE:FREQ=WEEKLY;INTERVAL=2;BYDAY=WE"
    ++ ev "count" "Counted out" "DTSTART:20261101T150000Z\nDTEND:20261101T160000Z\nRRULE:FREQ=DAILY;COUNT=2"
    ++ ev "until" "Until Tue" "DTSTART:20261101T150000Z\nDTEND:20261101T160000Z\nRRULE:FREQ=DAILY;UNTIL=20261103T235959Z"
    ++ ev "ex" "Skips Wed" "DTSTART:20261101T130000Z\nDTEND:20261101T133000Z\nRRULE:FREQ=DAILY\nEXDATE:20261104T130000Z"
    ++ ev "sync" "Sync" "DTSTART:20261101T200000Z\nDTEND:20261101T203000Z\nRRULE:FREQ=DAILY"
    ++ ev "sync" "Sync moved" "RECURRENCE-ID:20261103T200000Z\nDTSTART:20261103T220000Z\nDTEND:20261103T223000Z"
    ++ ev "sync" "Sync" "RECURRENCE-ID:20261104T200000Z\nDTSTART:20261104T200000Z\nDTEND:20261104T203000Z\nSTATUS:CANCELLED"
    ++ ev "yearly" "Anniversary" "DTSTART;VALUE=DATE:20201104\nRRULE:FREQ=YEARLY"
    ++ ev "bad" "Hourly" "DTSTART:20261101T150000Z\nRRULE:FREQ=HOURLY"
    ++ ev "span" "Conference" "DTSTART;VALUE=DATE:20261102\nDTEND;VALUE=DATE:20261105"
    ++ ev "late" "Overnight" "DTSTART:20261104T030000Z\nDTEND:20261104T070000Z"
    ++ "END:VCALENDAR\n")) (days 2026 11 3) none
  let seen := got.map fun e => s!"{e.day} {match e.start with
    | some ms => (hhmmss ((ms / 1000) % 86400) ":").take 5 |>.toString | none => "all-day"} {e.title}"
  -- Conference (all-day, Mon to Wed) and Overnight (Tue 22:00 to Wed 02:00 New York) list under both days.
  eq (strs seen) (strs ["2026-11-03 all-day Conference", "2026-11-03 13:00 Skips Wed", "2026-11-03 14:00 Tue Thu NY",
    "2026-11-03 15:00 Until Tue", "2026-11-03 17:00 First Tuesday", "2026-11-03 22:00 Sync moved", "2026-11-03 03:00 Overnight",
    "2026-11-04 all-day Anniversary", "2026-11-04 all-day Conference", "2026-11-04 03:00 Overnight",
    "2026-11-04 16:00 Every other Wed"]) "rules"
  eq (.bool ((← warned.get).contains "skipped \"Hourly\": can't expand its RRULE FREQ=HOURLY")) (.bool true) "warning"
  IO.println "ok"
  return 0

def sh (cmd : String) (env : Array (String × Option String) := #[]) : IO String := do
  return (← IO.Process.output { cmd := "sh", args := #["-c", cmd], env }).stdout

def main (args : List String) : IO UInt32 := do
  origTz.set (← IO.getEnv "TZ")
  let rec opts : List String → List (String × String)
    | a :: r => if a.startsWith "--" then (dropC a 2, (r.head?.getD "")) :: opts r else opts r
    | [] => []
  let a := opts args
  let opt (k : String) : Option String := (a.reverse.find? (·.1 == k)).map (·.2)
  if (opt "test").isSome then return ← selftest
  let dflt := ((← IO.getEnv "HOME").getD "") ++ "/.config/herdr-app"
  let home := match ← IO.getEnv "HERDR_APP_HOME" with | some h => if h != "" then h else dflt | none => dflt
  let mut conf : Json := .null
  if ← System.FilePath.pathExists (home ++ "/calendar.json" : String) then
    match Json.parse (← IO.FS.readFile (home ++ "/calendar.json" : String)) with
    | .ok c@(.obj _) | .ok c@(.arr _) => conf := c
    | _ => IO.eprintln s!"{home}/calendar.json is not a JSON object"; return 2
  let internal := match Json.field conf "internal_domains" with
    | some (.arr ds) => if ds.isEmpty then none else some (ds.toList.map fun
        | .str s => s.toLower | d => d.compress.toLower)
    | _ => none
  let ics ← match opt "ics" with
    | some f => IO.FS.readFile f
    | none => do
      let cmd := (Json.fstr conf "url_command").getD (if System.Platform.isOSX
        then "security find-generic-password -s herdr-gcal-ics -w" else "secret-tool lookup service herdr-gcal-ics")
      let url := stripN (← sh s!"({cmd}) 2>/dev/null")
      if url == "" then
        IO.eprintln s!"No calendar: `{cmd}` printed no iCal address. Set url_command in {home}/calendar.json"
        return 3
      -- through the environment, so the secret address never shows in a process list
      let ics ← sh "printf 'url = \"%s\"\\n' \"$ICS_URL\" | curl -fsSL --max-time 20 -K - 2>&1" #[("ICS_URL", some url)]
      if !hasSubL ics "BEGIN:VCALENDAR" then
        IO.eprintln s!"fetching the calendar failed: {cut (stripN ics) 300}"
        return 1
      pure ics
  let today ← match opt "date" with
    | some d => match (d.splitOn "-").map String.toInt? with
      | [some y, some m, some dd] => pure (days y m dd)
      | _ => throw <| IO.userError s!"bad --date {d}"
    | none => do
      match (← inTz none (strftime "%Y %m %d" (.ofInt (← now).toNat))).splitOn " " |>.filterMap String.toInt? with
      | [y, m, d] => pure (days y m d)
      | _ => throw <| IO.userError "localtime failed"
  IO.println (Json.arr ((← events (parse ics) today internal).map Rec.json).toArray).compress
  return 0

end SwarmLean.Herdr.Events
