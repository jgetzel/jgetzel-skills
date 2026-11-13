import HarnessRetro.Hr

/-! harness-lint.lua: check the harness mechanically and count what every session pays for.

    harness-lint.sh [--repo DIR] [--max-bytes N]

Always-on bytes: user and project CLAUDE.md (+ @imports), .claude/rules, the auto-memory MEMORY.md (first 200 lines).
Errors (exit 1): a skill without SKILL.md or description, a name that doesn't match its directory, a referenced skill
script that is missing or not executable, settings that don't parse, a hook command path that doesn't exist, a hook or
skill script that doesn't compile, always-on bytes over --max-bytes. -/

namespace HarnessRetro.Lint
open SwarmLean SwarmLean.Args
open Lean (Json)

/-- The hook events Claude Code knows. -/
def EVENTS : List String := words "PreToolUse PostToolUse PostToolUseFailure PermissionRequest PermissionDenied
  Notification UserPromptSubmit Stop StopFailure SubagentStart SubagentStop PreCompact PostCompact SessionStart SessionEnd
  Setup TeammateIdle TaskCreated TaskCompleted ConfigChange CwdChanged FileChanged InstructionsLoaded WorktreeCreate
  WorktreeRemove Elicitation ElicitationResult"

/-- What a run reports: errors and warnings, in the order found. -/
structure Out where
  errors : IO.Ref (Array String)
  warnings : IO.Ref (Array String)

/-- Records an error. -/
def Out.err (o : Out) (s : String) : IO Unit := o.errors.modify (·.push s)
/-- Records a warning. -/
def Out.warn (o : Out) (s : String) : IO Unit := o.warnings.modify (·.push s)

/-- A CLAUDE.md and the files it @imports, recursively, appended to `seen` (at most 51, like Claude Code). -/
partial def imports (o : Out) (h path : String) (seen : IO.Ref (Array String)) : IO Unit := do
  if (← seen.get).contains path then return
  if (← seen.get).size > 50 || !(← isfile path) then return
  seen.modify (·.push path)
  let text ← ok (Re.sub "```.*?```|`[^`\\n]*`" "" ((← read path).getD "") Re.S)
  for m in ← ok (Re.finditer "(?:^|\\s)@((?:~|\\.{1,2})?/?[\\w./-]+)" text) do
    let ref := (m.group 1).getD ""
    let p := normpath (joinPath (dirname path) (expanduser h ref))
    if ← isfile p then imports o h p seen
    else if hasSub ref "/" then o.warn s!"{path}: @{ref} not found"

/-- The always-on files and their sizes in bytes. -/
def alwaysOn (o : Out) (h repo : String) : IO (List (Nat × String)) := do
  let seen ← IO.mkRef #[]
  let cands := [h ++ "/.claude/CLAUDE.md"] ++
    (if repo != "" then ["/CLAUDE.md", "/CLAUDE.local.md", "/.claude/CLAUDE.md"].map (repo ++ ·) else [])
  for f in cands do imports o h f seen
  let mut files ← seen.get
  if repo != "" then
    files := files ++ (← walk (repo ++ "/.claude/rules") ".md")
    let common := (← git ["-C", repo, "rev-parse", "--path-format=absolute", "--git-common-dir"]).getD ""
    let root := if common.endsWith "/.git" then dirname common else repo
    let mem := s!"{h}/.claude/projects/{← ok (Re.sub "[^A-Za-z0-9]" "-" root)}/memory/MEMORY.md"
    if ← isfile mem then files := files.push mem
  files.toList.mapM fun f => do
    let data ← slurp f
    if f.endsWith "/memory/MEMORY.md" then  -- the first 200 lines, without the newline after the last
      let nls := (List.range data.size).filter (data[·]! == 10)
      if let some p := nls[199]? then return (p, f)
    return (data.size, f)

/-- Records an error when a script does not compile (python3, bash -n, luajit -b; a missing tool skips it). -/
def compiles (o : Out) (path : String) : IO Unit := do
  let lastLine (e : String) : String := ((e.splitOn "\n").reverse.dropWhile (· == "")).headD ""
  let err ← if path.endsWith ".py" then do
      let r ← exec ["python3", "-c",
        "import sys; compile(open(sys.argv[1], encoding='utf-8').read(), sys.argv[1], 'exec')", path]
      pure (if r.code != 0 && r.code != 127 then some s!"does not compile: {lastLine r.stderr}" else none)
    else if path.endsWith ".sh" then do
      let r ← exec ["bash", "-n", path]
      pure (if r.code != 0 then some s!"bash -n: {strip r.stderr}" else none)
    else if path.endsWith ".lua" then do
      let r ← exec ["luajit", "-b", path, "/dev/null"]
      pure (if r.code != 0 && r.code != 127 then some s!"does not compile: {strip r.stderr}" else none)
    else pure none
  if let some e := err then o.err s!"{path}: {e}"

/-- Each skill: SKILL.md, its frontmatter's description and name, the scripts it runs, and that they compile. -/
def skills (o : Out) (h repo : String) : IO Unit := do
  let repoSkills ← if repo != "" then subdirs (repo ++ "/.claude/skills") else pure []
  let dirs := (← subdirs (h ++ "/.claude/skills")) ++ repoSkills
  for dir in dirs do
    let name := basename dir
    let md := dir ++ "/SKILL.md"
    if !(← isfile md) then
      -- else a container of skills, e.g. a synced bundle
      unless (← walk dir "SKILL.md").any (basename · == "SKILL.md") do o.err s!"{dir}: no SKILL.md"
      continue
    let text := (← read md).getD ""
    let mut fm : List (String × String) := []
    if let some front ← ok (Re.match "---\\n(.*?)\\n---" text Re.S) then
      for m in ← ok (Re.finditer "^(\\w[\\w-]*):\\s*(.*)$" ((front.group 1).getD "") Re.M) do
        fm := ((m.group 1).getD "", (m.group 2).getD "") :: fm
    let quoteC (c : Char) : Bool := c == '"' || c == '\''
    let desc := String.ofList (((strip ((fm.lookup "description").getD "")).toList.dropWhile quoteC).reverse.dropWhile quoteC).reverse
    if desc == "" then o.err s!"{md}: no description in frontmatter (the skill never triggers)"
    else if desc.length > 1024 then o.warn s!"{md}: description is {desc.length} chars (limit 1024)"
    if let some n := fm.lookup "name" then
      if strip n != name then o.err s!"{md}: name '{strip n}' does not match directory '{name}'"
    for m in ← ok (Re.finditer "(\\b(?:python3?|luajit|bash|sh)\\s+)?(~/\\.claude/skills/[\\w./-]+\\.(?:sh|py|lua))" text) do
      let ref := (m.group 2).getD ""
      let p := expanduser h ref
      if !(← isfile p) then o.err s!"{md}: references {ref}, which does not exist"
      else if (m.group 1).isNone && (← exec ["test", "-x", p]).code != 0 then
        o.err s!"{md}: runs {ref} directly but it is not executable"
    for ext in [".py", ".sh", ".lua"] do
      for f in ← walk dir ext do compiles o f

/-- The settings files: they parse, their hook events are known, the scripts their hooks run exist and compile. -/
def settings (o : Out) (h repo : String) : IO Unit := do
  let files := [h ++ "/.claude/settings.json", h ++ "/.claude/settings.local.json"] ++
    (if repo != "" then [repo ++ "/.claude/settings.json", repo ++ "/.claude/settings.local.json"] else [])
  for f in files do
    unless ← isfile f do continue
    let cfg ← match Json.parse (lossy (← slurp f)) with
      | .ok c@(.obj _) | .ok c@(.arr _) => pure c
      | .ok _ => o.err s!"{f}: invalid JSON: nil"; continue
      | .error e => o.err s!"{f}: invalid JSON: {e}"; continue
    let hooks := match Json.field cfg "hooks" with | some (.obj kv) => kv.toArray.toList | _ => []
    for (event, entries) in hooks.mergeSort (fun a b => a.1 ≤ b.1) do
      if !EVENTS.contains event then o.warn s!"{f}: unknown hook event {event}"
      for e2 in arr (some entries) do
        for hk in arr (Json.field e2 "hooks") do
          let cmd := (Json.fstr hk "command").getD ""
          let toks ← ok (Re.finditer
            "(?:^|(?<=[\\s\"'=(]))((?:~|\\$HOME|\\$\\{HOME\\}|\\$CLAUDE_PROJECT_DIR|/)[^\\s\"';|&]*)" cmd)
          for m in toks do
            let tok := (m.group 1).getD ""
            if (← ok (Re.search "\\.(py|sh|lua)$|/bin/" tok)).isSome then
              let p := expanduser h (plainReplace (plainReplace (plainReplace tok "$CLAUDE_PROJECT_DIR" repo)
                "${HOME}" h) "$HOME" h)
              if (← kind p) == .none then o.err s!"{f}: {event} hook runs {tok}, which does not exist"
              else compiles o p

/-- The parser. -/
def spec : Spec :=
  .mk "harness-lint.sh" "Usage: harness-lint.sh [-h] [--repo <repo>] [--max-bytes <max_bytes>]

Options:
   -h, --help            Show this help message and exit.
   --repo <repo>         default: the cwd's git root
   --max-bytes <max_bytes>" [] [opt "--repo", opt "--max-bytes" (conv := some Args.int)] [] [] none

def main (args : List String) : IO UInt32 := do
  let some a ← parseArgs spec args | return 0
  let h ← home
  let o : Out := { errors := ← IO.mkRef #[], warnings := ← IO.mkRef #[] }
  let repo ← match a.str "repo" with
    | some r => pure r
    | none => (·.getD "") <$> git ["rev-parse", "--show-toplevel"]
  let rows ← alwaysOn o h repo
  let total : Nat := rows.foldl (· + ·.1) 0
  IO.println "## Always-on bytes"
  for (n, f) in rows do IO.println s!"{fmtD n 7}  {plainReplace f h "~"}"
  IO.println s!"{fmtD total 7}  total"
  if let some mx := a.int "max_bytes" then
    if mx != 0 && (total : Int) > mx then o.err s!"always-on is {total} bytes, over --max-bytes {mx}"
  skills o h repo
  settings o h repo
  for w in ← o.warnings.get do IO.println s!"warn: {w}"
  let errs ← o.errors.get
  for e in errs do IO.println s!"ERROR: {e}"
  IO.println (if errs.isEmpty then "ok" else s!"{errs.size} error(s)")
  return if errs.isEmpty then 0 else 1

end HarnessRetro.Lint
