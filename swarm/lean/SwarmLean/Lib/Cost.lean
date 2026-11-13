import SwarmLean.Sys
import SwarmLean.Lib.Machine

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

/-- A command shell the tick has seen open (a value of cost.open_cmds): whose, its command, wall seconds, peak RSS
(KiB), CPU seconds, and the agent's cgroup peak when it was the one open command as that rose. -/
structure OpenCmd where
  agent : String
  cmd : String
  wall : Int := 0
  peak : Int := 0
  cpu : Float := 0
  exact_kb : Option Int := none
  deriving Repr

/-- What the tick keeps between ticks (watchd's memory; a restart forgets it): each agent's cgroup peak at the last
tick (cost.cg_peak) and the open command shells by pid (cost.open_cmds). -/
structure TickMem where
  cgPeak : List (String × Int) := []
  opens : List (Int × OpenCmd) := []
  deriving Repr

/-- What one tick reads: the live agents' claude pids, each one's cgroup peak (KiB) where it has a cgroup, `ps`, the
processes' cwds, the repo's worktrees (none outside a repo), and the CPU seconds a shell's reaped children used. -/
structure TickIn where
  owners : List (Int × String)
  cgs : List (String × Int) := []
  procs : List Machine.Ps
  cwds : List (Int × String) := []
  wts : Option (List String) := none
  reaped : Int → Float := fun _ => 0

/-- A Bash-tool shell: its args name a shell snapshot. -/
def isShell (p : Machine.Ps) : Bool := hasSub p.args "/shell-snapshots/snapshot-"

/-- `p` is `w` or under it. -/
def inside (p : String) (dirs : List String) : Bool := dirs.any fun w => p == w || p.startsWith (w ++ "/")

/-- The first non-space word after `pre` followed by `sep` (one of its characters), as Lua's
`match("%s" .. pre .. sep .. "(%S+)")` finds it. -/
def argAfter (args pre : String) (seps : List Char) : Option String :=
  let s := args.toList
  let p := pre.toList
  (List.range s.length).findSome? fun i =>
    let r := s.drop i
    match r with
    | c :: r => if !isSpace c || !r.take p.length == p then none else
      let r := r.drop p.length
      let r := if seps == [' '] then (match r with | c :: _ => if isSpace c then r.dropWhile isSpace else [] | [] => [])
        else (match r with | c :: t => if seps.contains c then t else [] | [] => [])
      let w := r.takeWhile (!isSpace ·)
      if w.isEmpty then none else some (String.ofList w)
    | [] => none

/-- A user's own session's name: `user:<its -n or --name>`, a trailing `:` dropped, else `user`. -/
def userWho (args : String) : String :=
  let n := ((argAfter args "-n" [' ']).orElse fun _ => argAfter args "--name" [' ', '=']).getD ""
  let n := if n.endsWith ":" then (n.dropEnd 1).toString else n
  if n == "" then "user" else "user:" ++ n

/-- The shells under a claude process of no agent: the tick needs the repo's worktrees and the cwds only for these. -/
def needsUser (owners : List (Int × String)) (procs : List Machine.Ps) : Bool :=
  let by_ := Machine.byPid procs
  procs.any fun sh => isShell sh && (owners.lookup sh.ppid).isNone &&
    (by_.get? sh.ppid).any fun par => hasSub par.comm "claude"

/-- One watchd tick of the cmd-cost history (cost.tick): updates the open command shells and gives a row for each one
gone (ts `t`; machine and repo left empty, for the caller). User sessions (claude processes of no agent) count when
their cwd is in the repo. -/
def tickStep (mem : TickMem) (i : TickIn) (t : Int) : TickMem × List Rec := Id.run do
  let rose : List (String × Int) := i.cgs.filterMap fun (n, pk) =>
    match mem.cgPeak.lookup n with
    | some old => if pk > old then some (n, pk) else none
    | none => none
  let cgPeak := i.cgs.foldl (fun l (n, pk) => (n, pk) :: l.filter (·.1 != n)) mem.cgPeak
  let by_ := Machine.byPid i.procs
  let kids (pid : Int) := i.procs.filter (·.ppid == pid)
  let mut opens := mem.opens
  let mut seen : List Int := []
  let mut nopen : List (String × Nat) := []
  for sh in i.procs.filter isShell do
    let mut who := i.owners.lookup sh.ppid
    if who.isNone then
      if let some par := by_.get? sh.ppid then
        if hasSub par.comm "claude" then
          if let (some wts, some cw) := (i.wts, i.cwds.lookup par.pid) then
            if inside cw wts then who := some (userWho par.args)
    let some w := who | continue
    -- the shell's tree, breadth first; each level goes one process down, so as many levels as processes
    let mut rss : Int := 0
    let mut cpu : Int := 0
    let mut q := [sh]
    for _ in [0:i.procs.length + 1] do
      if q.isEmpty then break
      rss := rss + (q.map (·.rss_kb)).sum
      cpu := cpu + (q.map (·.cpu_s)).sum
      q := q.flatMap fun p => kids p.pid
    let o := match opens.lookup sh.pid with
      | some o => if sh.age < o.wall then none else some o  -- the pid was reused
      | none => none
    let o := o.getD { agent := w, cmd := (shellCmd sh.args).getD "?" }
    let o := { o with wall := sh.age, peak := max o.peak rss, cpu := max (max o.cpu (Float.ofInt cpu)) (i.reaped sh.pid) }
    opens := if (opens.lookup sh.pid).isSome then opens.map fun (p, x) => (p, if p == sh.pid then o else x)
      else opens ++ [(sh.pid, o)]
    seen := sh.pid :: seen
    nopen := (w, (nopen.lookup w).getD 0 + 1) :: nopen.filter (·.1 != w)
  -- the agent's cgroup peak rose while exactly one of its commands was open: that figure is the command's, exactly
  opens := opens.map fun (p, o) =>
    match seen.contains p, rose.lookup o.agent with
    | true, some kb => if nopen.lookup o.agent == some 1 then (p, { o with exact_kb := some kb }) else (p, o)
    | _, _ => (p, o)
  let gone := opens.filter fun (p, _) => !seen.contains p
  let recs := gone.map fun (_, o) =>
    let r : Rec := { ts := t, machine := "", repo := "", agent := o.agent, cmd := o.cmd, wall_s := o.wall,
                     cpu_s := o.cpu.floor.toInt64.toInt, peak_kb := max o.peak (o.exact_kb.getD 0),
                     exact := if o.exact_kb.isSome then 1 else 0 }
    r
  return ({ cgPeak, opens := opens.filter fun (p, _) => seen.contains p }, recs)

/-- Seconds of CPU a shell's reaped children used (Linux; fields 16 and 17 of /proc/<pid>/stat at 100 ticks a second),
0 where there is no such file. -/
def reapedCpu [Env m] [Fs m] (pid : Int) : m Float := do
  -- shortcut: CLK_TCK as 100 (Linux's on every common arch; Sys has no sysconf), upgrade if a machine differs
  let some s ← Fs.read s!"{← Machine.procRoot}/{d pid}/stat" | return 0
  match s.splitOn ")" with
  | _ :: _ :: _ =>
    let f := words ((s.splitOn ")").getLast!)
    let n (k : Nat) : Float := Float.ofInt ((f[k]?.bind parseInt).getD 0)
    return (n 13 + n 14) / 100
  | _ => return 0

/-- The repo's name and every worktree path, from the cwd (cost.lua's repo_info). -/
def repoInfo [Git m] : m (Option (String × List String)) := do
  let some name ← repoName | return none
  let ls := splitlines ((← Git.git ["worktree", "list", "--porcelain"] none).getD "")
  return some (name, ls.filterMap fun l => if l.startsWith "worktree " && l.length > 9 then some (l.drop 9).toString else none)

/-- watchd's cmd-cost tick (cost.tick) on `procs` (machine.procs) at `t`: reads the agents' cgroups (and, for user
sessions, the cwds and the repo's worktrees), runs `tickStep`, and writes a row for each finished command. -/
def tick [Store m] [Env m] [Fs m] [Proc m] [Sys m] [Git m] (mem : TickMem) (procs : List Machine.Ps) (t : Int) :
    m TickMem := do
  let agents ← Store.txn [.agent] fun db => (db, db.agents)
  let owners := Machine.claudeOwners agents
  let mut cgs := []
  for (pid, n) in owners do
    if let some cg ← Machine.cgroup pid then cgs := cgs ++ [(n, cg.peak_kb)]
  let (info, cwds) ← if needsUser owners procs then
      pure (← repoInfo, ((← Machine.cwds).getD []))
    else pure (none, [])
  let mut reaped := []
  for sh in procs.filter isShell do reaped := reaped ++ [(sh.pid, ← reapedCpu sh.pid)]
  let i : TickIn := { owners, cgs, procs, cwds, wts := info.map (·.2), reaped := fun p => (reaped.lookup p).getD 0 }
  let (mem, recs) := tickStep mem i t
  if !recs.isEmpty then
    let repo := ((← repoName).getD "?")
    let host ← Sys.hostname
    for r in recs do discard <| record { r with machine := host, repo }
  return mem

end SwarmLean.Cost
