import HarnessRetro.Hr
import Std.Data.HashMap

/-! time-report.lua: where the time went, tool wall time from Claude Code transcripts plus CI job time.

    time-report.sh [--since 2026-10-07T08:00] [--project-dir DIR]... [--top 15] [--no-ci]

Transcripts: every session in the project dir (the orchestrator and its herdr agents share one; repeat --project-dir
for agents that worked in another repo) whose records fall after --since (default: 24 h ago). A foreground tool call
runs from tool_use to tool_result; a background Bash call runs to its task-notification. Commands are grouped by what
they ran (`just test`, `gh pr checks`, ...), so the top rows are the optimization targets. CI: `gh run list` in the
cwd's repo, job and step durations for runs created after --since. -/

namespace HarnessRetro.TimeReport
open SwarmLean SwarmLean.Args
open Lean (Json)

/-- An ISO time from a transcript or gh, as epoch seconds. -/
def ts (s : String) : IO Float := do
  match ← parseIso s with
  | some t => return t
  | none => throw (IO.userError s!"bad timestamp {s}")

/-- A Bash command that loops waiting. -/
def WAIT_LOOP : Re.Pat := .lit "\\A\\s*(until|while|sleep)\\b"
/-- A Bash command that watches CI. -/
def CI_WATCH : Re.Pat := .lit "gh run watch|gh pr checks .*--watch"

/-- What a command ran, by tool: each pattern's first group names it. -/
def KEYS : List (String × Re.Pat) :=
  [("just", .lit "(?:^|[;&|(`]|\\bflock\\s+\\S+|--command)\\s*just\\s+([\\w-]+)"), ("gh", .lit "\\bgh\\s+(\\w+\\s+[\\w-]+)"),
   ("nix", .lit "\\bnix\\s+(\\w+)"), ("cabal", .lit "\\bcabal\\s+(\\w+)"), ("git", .lit "\\bgit\\s+([\\w-]+)"),
   ("herdr", .lit "\\bherdr\\s+(\\w+\\s+[\\w-]+)"), ("script", .lit "([\\w-]+\\.(?:sh|py|lua))\\b")]

/-- The row a tool call counts in. -/
def key (name : String) (inp : Json) : String :=
  let cmd := (Json.fstr inp "command").getD ""
  if name != "Bash" then name
  else if WAIT_LOOP.test cmd then "bash: wait loop"
  else if CI_WATCH.test cmd then "gh: wait for CI"
  else match KEYS.findSome? (fun (k, p) => (p.search cmd).map fun m => s!"{k} {(m.group 1).getD ""}") with
    | some r => r
    | none => s!"bash: {(words cmd).headD "?"}"

/-- A content value's text, blocks joined with a space, as time-report always did. -/
def textOf : Option Json → String
  | some (.str s) => s
  | c => " ".intercalate ((arr c).filterMap fun b =>
      match b with | .obj _ => some ((Json.fstr b "text").getD "") | _ => none)

/-- An orchestrator's brief naming an agent in bold. -/
def AGENT_BOLD : Re.Pat := .lit "agent \\*\\*([\\w-]+)\\*\\*"
/-- An agent brief's opening "You are <name>", maybe as pasted content. -/
def YOU_ARE : Re.Pat := .lit "\\A\\W*(?:<pasted_content[^>]*>\\s*)?You are \\**([a-z][\\w-]*)"

/-- A session's name: agent briefs open "You are <name>", sometimes as pasted content. -/
def label (first sid : String) : String :=
  match AGENT_BOLD.search first <|> YOU_ARE.search first with
  | some m => (m.group 1).getD ""
  | none => if hasSub first "orchestrat" then "orchestrator" else cut sid 8

/-- Total, count and max of some durations. -/
structure Row where
  total : Float := 0
  count : Nat := 0
  max : Float := 0

/-- Rows that remember the order their keys arrived in. -/
abbrev Rows := Array (String × Row)

/-- Adds a duration to key `k`'s row. -/
def add (t : Rows) (k : String) (dur : Float) : Rows :=
  let up (r : Row) : Row := { total := r.total + dur, count := r.count + 1, max := if dur > r.max then dur else r.max }
  match t.findIdx? (·.1 == k) with
  | some i => t.modify i fun (k, r) => (k, up r)
  | none => t.push (k, up {})

/-- Adds `v` to key `k`'s total. -/
def addF (t : Array (String × Float)) (k : String) (v : Float) : Array (String × Float) :=
  match t.findIdx? (·.1 == k) with
  | some i => t.modify i fun (k, x) => (k, x + v)
  | none => t.push (k, v)

/-- Waiting on CI, agents or the user, not doing work. -/
def WAITING : Re.Pat := .lit "watch\\.sh|wait loop|AskUserQuestion|wait for CI|gh pr checks|herdr agent wait"

/-- A task-notification's tool call. -/
def TOOL_USE_ID : Re.Pat := .lit "<tool-use-id>(\\w+)</tool-use-id>"

/-- A record: its kind (user, assistant, notify), time and content. -/
structure Rec where
  ty : String
  t : Float
  c : Option Json

/-- A tool call still open: its start, its row and whether it runs in the background. -/
abbrev Calls := Std.HashMap String (Float × String × Bool)

/-- The tool rows, each session's model and foreground tool time, and the current session's open calls and last
record. -/
structure Tally where
  tools : Rows := #[]
  model : Array (String × Float) := #[]
  per : Array (String × Float) := #[]
  uses : Calls := {}
  bg : Calls := {}
  prevkind : String := ""
  prevt : Float := 0

/-- Counts record `r` of session `who`. -/
def Tally.step (who : String) (s : Tally) (r : Rec) : Tally := Id.run do
  let c := r.c.getD (.str "")
  let mut s := s
  if r.ty == "assistant" then
    if s.prevkind == "tool" then s := { s with model := addF s.model who (r.t - s.prevt) }  -- model time after a tool result
    for b in arr (some c) do
      if Json.fstr b "type" == some "tool_use" then
        let inp := match Json.field b "input" with | some i@(.obj _) => i | _ => Json.mkObj []
        s := { s with uses := s.uses.insert ((Json.fstr b "id").getD "")
          (r.t, key ((Json.fstr b "name").getD "") inp, truthy (Json.field inp "run_in_background")) }
    return { s with prevkind := "asst", prevt := r.t }
  for m in TOOL_USE_ID.finditer (textOf (some c)) do
    let id := (m.group 1).getD ""
    if let some (t0, k, _) := s.bg[id]? then
      s := { s with bg := s.bg.erase id, tools := add s.tools s!"{k} (bg)" (r.t - t0) }
  if r.ty == "notify" then return s
  let mut isTool := false
  for b in arr (some c) do
    let id := (Json.fstr b "tool_use_id").getD ""
    if Json.fstr b "type" == some "tool_result" then
      if let some u@(t0, k, background) := s.uses[id]? then
        isTool := true
        s := { s with uses := s.uses.erase id }
        if background then s := { s with bg := s.bg.insert id u }
        else s := { s with tools := add s.tools k (r.t - t0), per := addF s.per who (r.t - t0) }
  return { s with prevkind := if isTool then "tool" else "human", prevt := r.t }

/-- Counts session `sid`'s records, named by its first user record. -/
def Tally.session (s : Tally) (sid : String) (recs : Array Rec) : Tally :=
  let first := match recs.find? (·.ty == "user") with
    | some r => textOf (r.c.getD (.str ""))
    | none => ""
  recs.foldl (Tally.step (label first sid)) { s with uses := {}, bg := {}, prevkind := "", prevt := 0 }

/-- The tally of some sessions, each its id and records. -/
def tally (ss : Array (String × Array Rec)) : Tally := ss.foldl (fun t (sid, recs) => t.session sid recs) {}

/-- Each session in `pdirs` modified since `since`: its id and its records since then. -/
def sessions (pdirs : List String) (since : Float) : IO (Array (String × Array Rec)) := do
  let mut files := #[]
  for dir in pdirs do
    for f in ← walk dir ".jsonl" do
      if f.startsWith (dir ++ "/") && !hasSub (f.drop (dir.length + 1)).toString "/" then files := files.push f
  let mut out : Array (String × Array Rec) := #[]
  for f in files do
    let some mt ← (try some <$> System.FilePath.metadata f catch _ => pure none) | continue
    if Float.ofInt mt.modified.sec < since then continue
    let mut recs : Array Rec := #[]
    for line in ((← read f).getD "").splitOn "\n" do
      let some r := Json.decode line | continue
      let ty := (Json.fstr r "type").getD ""
      let some stamp := Json.fstr r "timestamp" | continue
      if (ty == "user" || ty == "assistant") && !(Json.field r "isSidechain" |>.any (· != .bool false)) then
        recs := recs.push { ty, t := ← ts stamp, c := (Json.field r "message").bind (Json.field · "content") }
      if ty == "queue-operation" && Json.fstr r "operation" == some "enqueue" then  -- task-notifications
        recs := recs.push { ty := "notify", t := ← ts stamp, c := some ((Json.field r "content").getD (.str "")) }
    recs := recs.filter (·.t ≥ since)
    if !recs.isEmpty then out := out.push (basename f, recs)
  return out

/-- A `gh run view --json jobs` output's jobs. -/
def jobsOf (out : String) : List Json :=
  match Json.decode (if out != "" then out else "{\"jobs\":[]}") with
  | some j => arr (Json.field j "jobs")
  | none => []

/-- CI since `since`: the number of runs, the job rows and the step totals. -/
def ci (since : Float) : IO (Nat × Rows × Array (String × Float)) := do
  let q := ".[]|select(.createdAt >= \"" ++ isoUtc since.floor.toInt64.toInt ++ "\")|.databaseId"
  let out ← exec ["gh", "run", "list", "--limit", "100", "--json", "databaseId,createdAt", "--jq", q]
  let ids := words out.stdout
  let mut jobs : Rows := #[]
  let mut steps : Array (String × Float) := #[]
  for i in ids do
    let jo ← exec ["gh", "run", "view", i, "--json", "jobs"]
    for j in jobsOf jo.stdout do
      let some done := Json.fstr j "completedAt" | continue
      if done.startsWith "0001" then continue
      let dur := (← ts done) - (← ts ((Json.fstr j "startedAt").getD ""))
      if Json.fstr j "conclusion" == some "skipped" || dur < 0 then continue
      let name := (Json.fstr j "name").getD ""
      jobs := add jobs name dur
      for s in arr (Json.field j "steps") do
        let some sd := Json.fstr s "completedAt" | continue
        if sd.startsWith "0001" then continue
        steps := addF steps s!"{name} › {(Json.fstr s "name").getD ""}" ((← ts sd) - (← ts ((Json.fstr s "startedAt").getD "")))
  return (ids.length, jobs, steps)

/-- Seconds as minutes, `%6.1fm`. -/
def fmt (s : Float) : String := fmtF (s / 60) 6 1 ++ "m"

/-- A row: total, count, max and its key. -/
def rowLine (k : String) (r : Row) : String := s!"{fmt r.total} {fmtD r.count 4}× max {fmt r.max}   {k}"

/-- A positive integer option (Lua's tonumber), else malformed. -/
def num : Conv := fun s => match parseInt s with
  | some n => .ok (.i n)
  | none => .error none

/-- The parser. -/
def spec : Spec :=
  .mk "time-report.sh" "Usage: time-report.sh [-h] [--since <since>]
       [--project-dir <project_dir>] [--top <top>] [--no-ci]

Options:
   -h, --help            Show this help message and exit.
   --since <since>       ISO time (local if no zone); default 24 h ago
   --project-dir <project_dir>
                         repeatable; default: the cwd's project dir
   --top <top>           default: 15
   --no-ci" [] [opt "--since", { opt "--project-dir" with maxCount := 1000000 }, opt "--top" (conv := some num),
    flag "--no-ci"] [] [] none

def main (args : List String) : IO UInt32 := do
  let some a ← parseArgs spec args | return 0
  let top := (a.int "top").getD 15 |>.toNat
  let mut since : Float := Float.ofNat ((← Sqlite.now).toNat - 24 * 3600)
  if let some s := a.str "since" then
    match ← parseIso s with
    | some t => since := t
    | none => IO.eprintln s!"time-report.sh: error: bad --since {s}"; return 2
  let cwdDir := s!"{← home}/.claude/projects/{NON_ALNUM.sub "-" (← IO.currentDir).toString}"
  let pdirs := match a.strs "project_dir" with
    | [] => [cwdDir]
    | ds => ds
  let t := tally (← sessions pdirs since)
  let (tools, model, per) := (t.tools, t.model, t.per)
  IO.println s!"# Time report since {← Shim.strftime "%Y-%m-%d %H:%M" (Int64.ofInt since.floor.toInt64.toInt)}\n\n## Sessions (foreground tool time · model time)"
  let get (t : Array (String × Float)) (w : String) : Float := ((t.find? (·.1 == w)).map (·.2)).getD 0
  let whos := ((per.map (·.1)) ++ (model.map (·.1)).filter (fun w => !per.any (·.1 == w))).toList.mergeSort (· ≤ ·)
  for who in sortedBy whos (fun w => -(get per w + get model w)) do
    IO.println s!"{fmt (get per who)} tools · {fmt (get model who)} model   {who}"
  for (title, waiting) in [("Work", false), ("Waiting (CI, agents, user)", true)] do
    IO.println s!"\n## {title}: tool time, all sessions (total · calls · max)"
    let list := tools.toList.filter fun (k, _) => WAITING.test k == waiting
    for (k, r) in (sortedBy list (fun (_, r) => -r.total)).take top do IO.println (rowLine k r)
  if !a.flag "no_ci" then
    let (n, jobs, steps) ← ci since
    IO.println s!"\n## CI: {n} runs (total · runs · max)"
    for (k, r) in sortedBy jobs.toList (fun (_, r) => -r.total) do IO.println (rowLine k r)
    IO.println "\n## CI: top steps (total)"
    for (k, s) in (sortedBy steps.toList (fun (_, s) => -s)).take top do IO.println s!"{fmt s}   {k}"
  return 0

end HarnessRetro.TimeReport
