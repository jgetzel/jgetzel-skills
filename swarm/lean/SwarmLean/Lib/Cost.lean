import SwarmLean.Sys

/-! cost.lua: the cmd-cost history (one row per finished command that cost something), outside swarm.db, per user and
machine: the key a command is filed under, the summary `swarm cost` prints, the prediction the hook shows. watchd's
tick (which writes the rows) is `tick`, pure over its readings. -/

namespace SwarmLean.Cost
open Sqlite (Val)

variable {m : Type → Type} [Monad m]

/-- Rows kept per (machine, repo, key). -/
def KEEP : Nat := 20
/-- A command is recorded when it ran this long (s)... -/
def MIN_WALL : Int := 60
/-- ... or peaked this high (KiB). -/
def MIN_PEAK_KB : Int := 1048576

/-- The history's schema (cmd-cost.md). -/
def SCHEMA : String := "
create table if not exists cmd(id integer primary key, ts int, machine text, repo text, agent text, source text,
  cmd text, key text, wall_s int, cpu_s int, peak_kb int, exact int);
create index if not exists cmd_key on cmd(machine, repo, key, id);
"

/-- The history file: $XDG_STATE_HOME (else ~/.local/state)/cmd-cost/history.db. -/
def path [Env m] : m String := do
  let x ← match ← Env.var "XDG_STATE_HOME" with
    | some x => if x != "" then pure x else pure (((← Env.var "HOME").getD "") ++ "/.local/state")
    | none => pure (((← Env.var "HOME").getD "") ++ "/.local/state")
  return x ++ "/cmd-cost/history.db"

/-- `^cd%s+[^&;]+&&%s*` stripped, if it matches. -/
def dropCd : List Char → Option (List Char)
  | 'c' :: 'd' :: rest =>
    let sp := rest.takeWhile isSpace
    let r := rest.drop sp.length
    let body := r.takeWhile fun c => c != '&' && c != ';'
    if sp.isEmpty || body.isEmpty then none else
    match r.drop body.length with
    | '&' :: '&' :: t => some (t.dropWhile isSpace)
    | _ => none
  | _ => none

/-- Index of the first `%s%-%-%s+` at or after `i`, and the index after it. -/
def dashes (s : List Char) (i : Nat) : Option Nat :=
  (List.range (s.length - i)).findSome? fun k =>
    let j := i + k
    match s.drop j with
    | c :: '-' :: '-' :: d :: t => if isSpace c && isSpace d then some (s.length - (t.dropWhile isSpace).length) else none
    | _ => none

/-- `^swarm%s+run%s.-%s%-%-%s+` stripped, if it matches. -/
def dropRun (s : List Char) : Option (List Char) :=
  if !(String.ofList s).startsWith "swarm" then none else
  let sp := (s.drop 5).takeWhile isSpace
  let r := (s.drop 5).drop sp.length
  match r with
  | 'r' :: 'u' :: 'n' :: c :: _ =>
    if sp.isEmpty || !isSpace c then none else
    let i := s.length - r.length + 4
    (dashes s i).map (s.drop ·)
  | _ => none

/-- `^[%a_][%w_]*=%S*%s+` stripped, if it matches. -/
def dropAssign : List Char → Option (List Char)
  | c :: rest =>
    if !(c.isAlpha || c == '_') then none else
    let r := rest.dropWhile fun x => x.isAlphanum || x == '_'
    match r with
    | '=' :: t =>
      let v := t.dropWhile (!isSpace ·)
      if v.isEmpty || !isSpace v.head! then none else some (v.dropWhile isSpace)
    | _ => none
  | [] => none

/-- `s:gsub("%s*|.*$", "")`: cut at the first `|`, with the spaces before it. -/
def cutPipe (s : List Char) : List Char :=
  match s.findIdx? (· == '|') with
  | some i => ((s.take i).reverse.dropWhile isSpace).reverse
  | none => s

/-- `s:gsub("%s+%d*[<>].*$", "")`: cut at the first spaces followed by a redirection. -/
def cutRedir (s : List Char) : List Char :=
  let hit (j : Nat) : Bool :=
    let t := s.drop j
    match t with
    | c :: _ => isSpace c && match (t.dropWhile isSpace).dropWhile Char.isDigit with
      | x :: _ => x == '<' || x == '>'
      | [] => false
    | [] => false
  match (List.range s.length).find? hit with
  | some j => s.take j
  | none => s

/-- The command with a leading `cd … &&`, `swarm run … --`, environment assignments and trailing pipes and redirections
stripped, cut to its first three words (cost.key). -/
def key (cmd : String) : String :=
  let rec strip1 (fuel : Nat) (s : List Char) : List Char :=
    match fuel with
    | 0 => s
    | f + 1 =>
      let s' := (dropCd s).getD s
      let s' := (dropRun s').getD s'
      let s' := (dropAssign s').getD s'
      if s'.length == s.length then s else strip1 f s'
  let s := strip1 cmd.length (strip cmd).toList
  let s := String.ofList (cutRedir (cutPipe s))
  " ".intercalate ((words s).take 3)

/-- The command a Bash-tool shell was asked to run: `eval '<cmd>' \< /dev/null && …` (cost.shell_cmd). -/
def shellCmd (args : String) : Option String :=
  let s := args.toList
  let n := s.length
  -- the body after the first `eval%s+` at or after i, its start
  let evalAt (j : Nat) : Option Nat :=
    match s.drop j with
    | 'e' :: 'v' :: 'a' :: 'l' :: c :: t => if isSpace c then some (n - (t.dropWhile isSpace).length) else none
    | _ => none
  let devnull (e : Nat) : Bool :=
    match s.drop e with
    | c :: _ => isSpace c && match (s.drop e).dropWhile isSpace with
      | '\\' :: '<' :: d :: t => isSpace d && (String.ofList (t.dropWhile isSpace)).startsWith "/dev/null"
      | _ => false
    | [] => false
  let first : Option (List Char) := (List.range n).findSome? fun j =>
    (evalAt j).bind fun q => ((List.range (n - q)).find? fun k => devnull (q + k)).map fun k => (s.drop q).take k
  let body := match first with
    | some b => some b
    | none => ((List.range n).findSome? evalAt).map (s.drop ·)
  body.map fun b =>
    let b := match b with | '\'' :: t => t | t => t
    let b := if b.getLast? == some '\'' then b.dropLast else b
    (String.ofList b).replace "'\\''" "'"

/-- An integer cell (a float floored, NULL 0). -/
def vi : Val → Int
  | .int i => i
  | .real f => f.floor.toInt64.toInt
  | .text t => (parseInt t).getD 0
  | .null => 0

/-- A text cell. -/
def vs : Val → String
  | .text t => t
  | .int i => toString i
  | .real f => toString f
  | .null => ""

/-- The median as cost.lua takes it: the lower middle of the sorted values, 0 for none. -/
def median (a : List Int) : Int := ((a.mergeSort (· ≤ ·))[(a.length + 1) / 2 - 1]?).getD 0

/-- `%d min` of seconds, at least 1, rounded. -/
def mins (s : Int) : String := s!"{max 1 (fdiv (2 * s + 60) 120)} min"

/-- `%.1fG` of KiB. -/
def gib (kb : Int) : String := s!"{fixed (Float.ofInt kb / 1048576) 1}G"

/-- Seconds as whole minutes, rounded half up (math.floor(s / 60 + 0.5)). -/
def cpuMin (s : Int) : Int := fdiv (2 * s + 60) 120

/-- The summary line of (wall_s, cpu_s, peak_kb) rows of `key` (cost.summary), none without rows. -/
def summaryOf (key : String) (rows : List (Int × Int × Int)) : Option String :=
  if rows.isEmpty then none else
  let w := rows.map (·.1)
  let cp := rows.map (·.2.1)
  let pk := rows.map (·.2.2)
  let mx := pk.foldl max 0
  some s!"`{key}`, this repo, this machine: {rows.length} run{if rows.length == 1 then "" else "s"}, median {mins (median w)}, peak {gib (median pk)} (max {gib mx}), {cpuMin (median cp)} CPU-min."

/-- A row to record (cost.record's r). -/
structure Rec where
  ts : Int
  machine : String
  repo : String
  agent : String
  source : String := "swarm"
  cmd : String
  key : Option String := none
  wall_s : Int
  cpu_s : Int := 0
  peak_kb : Int
  exact : Int := 0

/-- cost.record's statements: none when the command was short and small; else the insert and the pruning. -/
def recordSql (r : Rec) : Option (List (String × List Val)) :=
  if !(r.wall_s ≥ MIN_WALL || r.peak_kb ≥ MIN_PEAK_KB) then none else
  let k := r.key.getD (key r.cmd)
  some [("insert into cmd(ts,machine,repo,agent,source,cmd,key,wall_s,cpu_s,peak_kb,exact) values(?,?,?,?,?,?,?,?,?,?,?)",
      [.int r.ts, .text r.machine, .text r.repo, .text r.agent, .text r.source, .text r.cmd, .text k, .int r.wall_s,
       .int r.cpu_s, .int r.peak_kb, .int r.exact]),
    ("delete from cmd where machine=? and repo=? and key=? and id not in (select id from cmd where machine=? and repo=? " ++
      "and key=? order by id desc limit ?)", [.text r.machine, .text r.repo, .text k, .text r.machine, .text r.repo, .text k,
      .int KEEP])]

/-- Writes a row to the history (cost.record); false when it was too cheap to keep. -/
def record [Env m] [Sys m] (r : Rec) : m Bool := do
  match recordSql r with
  | some st => discard <| Sys.sqlAt (← path) SCHEMA st; return true
  | none => return false

/-- The repo's name (its main checkout's directory) as seen from `cwd` (cost.repo_name). -/
def repoName [Git m] (cwd : Option String := none) : m (Option String) := do
  let some common := (← Git.git ["rev-parse", "--path-format=absolute", "--git-common-dir"] cwd).map strip | return none
  if common == "" then return none
  return some (basename (dirname common))

/-- Whether the history file exists (the hook never creates it). -/
def exists? [Env m] [Sys m] : m Bool := return (← Sys.kind (← path) true) != .none

/-- What the history predicts for a command about to run (cost.predict): runs, median wall and peak, its key. -/
structure Prediction where
  n : Nat
  wall_s : Int
  peak_kb : Int
  key : String

/-- cost.predict: none without the file or rows for the command here. -/
def predict [Env m] [Sys m] [Git m] (cmd : String) (cwd : Option String) : m (Option Prediction) := do
  if !(← exists?) then return none
  let some repo ← repoName cwd | return none
  let k := key cmd
  let rows := ((← Sys.sqlAt (← path) SCHEMA [("select wall_s,peak_kb from cmd where machine=? and repo=? and key=?",
    [.text (← Sys.hostname), .text repo, .text k])]).headD #[]).toList
  if rows.isEmpty then return none
  return some { n := rows.length, wall_s := median (rows.map fun r => vi (r.getD 0 .null)),
                peak_kb := median (rows.map fun r => vi (r.getD 1 .null)), key := k }

end SwarmLean.Cost
