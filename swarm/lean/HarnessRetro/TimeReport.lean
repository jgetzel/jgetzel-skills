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

/-- What a command ran, by tool: each pattern's first group names it. -/
def KEYS : List (String × String) :=
  [("just", "(?:^|[;&|(`]|\\bflock\\s+\\S+|--command)\\s*just\\s+([\\w-]+)"), ("gh", "\\bgh\\s+(\\w+\\s+[\\w-]+)"),
   ("nix", "\\bnix\\s+(\\w+)"), ("cabal", "\\bcabal\\s+(\\w+)"), ("git", "\\bgit\\s+([\\w-]+)"),
   ("herdr", "\\bherdr\\s+(\\w+\\s+[\\w-]+)"), ("script", "([\\w-]+\\.(?:sh|py|lua))\\b")]

/-- The row a tool call counts in. -/
def key (name : String) (inp : Json) : IO String := do
  if name != "Bash" then return name
  let cmd := (Json.fstr inp "command").getD ""
  if (← ok (Re.match "\\s*(until|while|sleep)\\b" cmd)).isSome then return "bash: wait loop"
  if (← ok (Re.search "gh run watch|gh pr checks .*--watch" cmd)).isSome then return "gh: wait for CI"
  for (k, pat) in KEYS do
    if let some m ← ok (Re.search pat cmd) then return s!"{k} {(m.group 1).getD ""}"
  return s!"bash: {(words cmd).headD "?"}"

/-- A content value's text, blocks joined with a space, as time-report always did. -/
def textOf : Option Json → String
  | some (.str s) => s
  | c => " ".intercalate ((arr c).filterMap fun b =>
      match b with | .obj _ => some ((Json.fstr b "text").getD "") | _ => none)

/-- A session's name: agent briefs open "You are <name>", sometimes as pasted content. -/
def label (first sid : String) : IO String := do
  let m ← match ← ok (Re.search "agent \\*\\*([\\w-]+)\\*\\*" first) with
    | some m => pure (some m)
    | none => ok (Re.search "\\A\\W*(?:<pasted_content[^>]*>\\s*)?You are \\**([a-z][\\w-]*)" first)
  if let some m := m then return (m.group 1).getD ""
  if hasSub first "orchestrat" then return "orchestrator"
  return cut sid 8

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
def WAITING := "watch\\.sh|wait loop|AskUserQuestion|wait for CI|gh pr checks|herdr agent wait"

/-- A record: its kind (user, assistant, notify), time and content. -/
structure Rec where
  ty : String
  t : Float
  c : Option Json

/-- The tool rows, and each session's model and foreground tool time. -/
def sessions (pdirs : List String) (since : Float) : IO (Rows × Array (String × Float) × Array (String × Float)) := do
  let mut tools : Rows := #[]
  let mut model : Array (String × Float) := #[]
  let mut per : Array (String × Float) := #[]
  let mut files := #[]
  for dir in pdirs do
    for f in ← walk dir ".jsonl" do
      if f.startsWith (dir ++ "/") && !hasSub (f.drop (dir.length + 1)).toString "/" then files := files.push f
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
    if recs.isEmpty then continue
    let first := match recs.find? (·.ty == "user") with
      | some r => textOf (r.c.getD (.str ""))
      | none => ""
    let who ← label first (basename f)
    let mut uses : Std.HashMap String (Float × String × Bool) := {}
    let mut bg : Std.HashMap String (Float × String × Bool) := {}
    let mut prevkind := ""
    let mut prevt : Float := 0
    for r in recs do
      let c := r.c.getD (.str "")
      if r.ty == "assistant" then
        if prevkind == "tool" then model := addF model who (r.t - prevt)  -- model time after a tool result
        for b in arr (some c) do
          if Json.fstr b "type" == some "tool_use" then
            let inp := match Json.field b "input" with | some i@(.obj _) => i | _ => Json.mkObj []
            uses := uses.insert ((Json.fstr b "id").getD "") (r.t, ← key ((Json.fstr b "name").getD "") inp,
              truthy (Json.field inp "run_in_background"))
        prevkind := "asst"; prevt := r.t
        continue
      for m in ← ok (Re.finditer "<tool-use-id>(\\w+)</tool-use-id>" (textOf (some c))) do
        let id := (m.group 1).getD ""
        if let some (t0, k, _) := bg[id]? then
          bg := bg.erase id
          tools := add tools s!"{k} (bg)" (r.t - t0)
      if r.ty != "notify" then
        let mut isTool := false
        for b in arr (some c) do
          let id := (Json.fstr b "tool_use_id").getD ""
          if Json.fstr b "type" == some "tool_result" then
            if let some u@(t0, k, background) := uses[id]? then
              isTool := true
              uses := uses.erase id
              if background then bg := bg.insert id u
              else
                tools := add tools k (r.t - t0)
                per := addF per who (r.t - t0)
        prevkind := if isTool then "tool" else "human"
        prevt := r.t
  return (tools, model, per)

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
  let cwdDir := s!"{← home}/.claude/projects/{← ok (Re.sub "[^A-Za-z0-9]" "-" (← IO.currentDir).toString)}"
  let pdirs := match a.strs "project_dir" with
    | [] => [cwdDir]
    | ds => ds
  let (tools, model, per) ← sessions pdirs since
  IO.println s!"# Time report since {← Shim.strftime "%Y-%m-%d %H:%M" (Int64.ofInt since.floor.toInt64.toInt)}\n\n## Sessions (foreground tool time · model time)"
  let get (t : Array (String × Float)) (w : String) : Float := ((t.find? (·.1 == w)).map (·.2)).getD 0
  let whos := ((per.map (·.1)) ++ (model.map (·.1)).filter (fun w => !per.any (·.1 == w))).toList.mergeSort (· ≤ ·)
  for who in sortedBy whos (fun w => -(get per w + get model w)) do
    IO.println s!"{fmt (get per who)} tools · {fmt (get model who)} model   {who}"
  for (title, waiting) in [("Work", false), ("Waiting (CI, agents, user)", true)] do
    IO.println s!"\n## {title}: tool time, all sessions (total · calls · max)"
    let list ← tools.toList.filterM fun (k, _) => return (← ok (Re.search WAITING k)).isSome == waiting
    for (k, r) in (sortedBy list (fun (_, r) => -r.total)).take top do IO.println (rowLine k r)
  if !a.flag "no_ci" then
    let (n, jobs, steps) ← ci since
    IO.println s!"\n## CI: {n} runs (total · runs · max)"
    for (k, r) in sortedBy jobs.toList (fun (_, r) => -r.total) do IO.println (rowLine k r)
    IO.println "\n## CI: top steps (total)"
    for (k, s) in (sortedBy steps.toList (fun (_, s) => -s)).take top do IO.println s!"{fmt s}   {k}"
  return 0

end HarnessRetro.TimeReport
