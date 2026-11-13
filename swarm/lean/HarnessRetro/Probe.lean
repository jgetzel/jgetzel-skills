import HarnessRetro.Hr

/-! probe-guard.lua and probe-json.lua: the PreToolUse guard that keeps a harness-retro probe replay inside its checkout,
and probe.sh's JSON helpers.

    probe-guard.sh WORKTREE MAIN_REPO      (hook; event JSON on stdin)
    probe-guard.sh --selftest
    probe-json.sh get PATH                 (JSON on stdin as d) print d.a.b; `P or Q` tries P, then Q
    probe-json.sh settings CMD...          print a settings.json whose PreToolUse hook runs the quoted CMD

The guard allows a fixed set of local tools. It denies anything that reaches outside the checkout: pushes, PRs, ssh,
herdr, messages to other agents, shared git refs, writes outside the worktree and /tmp, and any command naming the main
repo. -/

namespace HarnessRetro.Probe
open SwarmLean
open Lean (Json)

/-- The tools a replay may use. -/
def TOOLS : List String := words "Read Write Edit MultiEdit NotebookEdit Bash Glob Grep LS ToolSearch Skill TodoWrite
  Task Agent Monitor TaskStop TaskOutput BashOutput KillShell WebFetch WebSearch"

-- shortcut: a denylist on command text, not a sandbox; Bash can still write outside via a script it wrote.
/-- Commands that leave the replay. -/
def DENY : String :=
  "\\bgit\\s+(push|worktree|tag|update-ref|stash|branch\\s+(-[dDmMcC]\\b|[^-\\s])|checkout\\s+-[bB]|switch\\s+-[cC])" ++
  "|\\bgh\\s+(pr|issue|release|repo|api|workflow|run\\s+(rerun|cancel))\\b" ++
  "|\\b(ssh|scp|rsync|herdr|pkill|killall)\\b|\\b(npm|cargo|uv)\\s+publish\\b|\\bdocker\\s+push\\b" ++
  "|\\bcurl\\b[^|;&]*-X\\s*(POST|PUT|PATCH|DELETE)"

/-- Why a tool call leaves the replay of worktree `wt` (main repo `main`), or none. -/
def verdict (h : String) (ev : Json) (wt main : String) : IO (Option String) := do
  let tool := (Json.fstr ev "tool_name").getD ""
  let inp := (Json.field ev "tool_input").getD (Json.mkObj [])
  if !TOOLS.contains tool then return some s!"{tool} reaches outside this sandboxed replay"
  if truthy (Json.field inp "isolation") then return some "worktree isolation creates shared git refs; work in this checkout"
  let cmd := (Json.fstr inp "command").getD ""
  if cmd != "" then
    if let some m ← ok (Re.search DENY cmd) then return some s!"`{strip m.whole}` leaves this sandboxed replay"
    for p in [main, plainReplace main h "~"] do
      if (← ok (Re.search (Re.escape p ++ "(/|\\s|$|['\"])") cmd)).isSome then
        return some s!"{main} is the live repo; use this checkout ({wt})"
  let path := match Json.field inp "file_path" with
    | some (.bool false) | none => Json.field inp "notebook_path"
    | p => p
  if truthy path && !["Read", "Glob", "Grep", "LS"].contains tool then
    let ps := match path with | some (.str s) => s | _ => ""
    let p ← realpath (expanduser h ps)
    let w ← realpath wt
    if !(p == w || p.startsWith (w ++ "/") || p == "/tmp" || p.startsWith "/tmp/") then
      return some s!"write to {ps} is outside this checkout"
  return none

/-- The guard's cases: what it must deny and allow. -/
def selftest : IO UInt32 := do
  let h ← home
  let wt := "/w/.r-worktrees/probe-1-a"
  let main := h ++ "/r"
  let allowed (t : String) (i : List (String × Json)) : IO Bool := do
    return (← verdict h (Json.mkObj [("tool_name", t), ("tool_input", Json.mkObj i)]) wt main).isNone
  let cmd (c : String) : List (String × Json) := [("command", c)]
  let file (f : String) : List (String × Json) := [("file_path", f)]
  let cases : List (Bool × String × List (String × Json)) := [
    (false, "Bash", cmd "git commit -m 'ssh fix'"),  -- matches inside quotes too, deliberately
    (true, "Bash", cmd "just test && git commit -am wip"),
    (false, "Bash", cmd "git push origin HEAD"),
    (false, "Bash", cmd "bash -c 'gh pr create'"),
    (false, "Bash", cmd "git branch -D other"),
    (true, "Bash", cmd "git branch --show-current"),
    (false, "Bash", cmd s!"cd {main} && ls"),
    (false, "Bash", cmd "git -C ~/r log"),
    (true, "Bash", cmd "ls ~/rx"),
    (false, "Monitor", cmd "ssh desktop tail -F log"),
    (false, "SendMessage", [("to", "wf-ml"), ("message", "hi")]),
    (false, "Agent", [("prompt", "x"), ("isolation", "worktree")]),
    (true, "Write", file (wt ++ "/a.py")),
    (true, "Write", file "/tmp/x"),
    (false, "Write", file (wt ++ "/../../x")),
    (false, "Write", file (h ++ "/.claude/projects/r/memory/m.md")),
    (true, "Read", file "/etc/hosts")]
  for (want, t, i) in cases do
    if (← allowed t i) != want then
      IO.eprintln s!"probe-guard selftest failed: {t} {(Json.mkObj i).compress} should be {if want then "allowed" else "denied"}"
      return 1
  IO.println "probe-guard selftest ok"
  return 0

/-- probe-guard: the hook, or `--selftest`. -/
def guard (args : List String) : IO UInt32 := do
  if args == ["--selftest"] then return ← selftest
  let some ev := Json.decode (← (← IO.getStdin).readToEnd) | IO.eprintln "probe-guard: stdin is not JSON"; return 1
  if let some why ← verdict (← home) ev (args.headD "") (args.getD 1 "") then
    IO.eprintln s!"Blocked by harness-retro probe-guard: {why}. This is a sandboxed replay; note what you would have done and continue locally."
    return 2
  return 0

/-- The value at a dotted path from `d` (`d.result.tab.id`), none when a step is missing. -/
def path (doc : Json) (p : String) : Option Json :=
  ((strip p).splitOn ".").drop 1 |>.foldlM (fun j k => Json.field j k) doc

/-- A value as probe.sh reads it: a string bare, a number in Lua's form, other JSON as text, nothing as "". -/
def shown : Option Json → String
  | none | some .null => ""
  | some (.str s) => s
  | some (.num n) => if n.exponent == 0 then toString n.mantissa else toString n
  | some (.bool b) => toString b
  | some j => j.compress

/-- probe-json: `get PATH [or PATH]...` or `settings CMD...`. -/
def json (args : List String) : IO UInt32 := do
  match args with
  | ["get", expr] =>
    let some doc := Json.decode (← (← IO.getStdin).readToEnd) | IO.eprintln "probe-json: stdin is not JSON"; return 1
    IO.println (shown (((expr.splitOn " or ").map (path doc)).findSome? id))
    return 0
  | "settings" :: cmd =>
    let hook := Json.mkObj [("type", "command"), ("command", shjoin cmd), ("timeout", 10)]
    let entry := Json.mkObj [("matcher", ""), ("hooks", Json.arr #[hook])]
    IO.println (Json.mkObj [("hooks", Json.mkObj [("PreToolUse", Json.arr #[entry])])]).compress
    return 0
  | _ => IO.eprintln "usage: probe-json.sh get PATH | settings CMD..."; return 2

end HarnessRetro.Probe
