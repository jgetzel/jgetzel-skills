import SwarmLean.Lib.Re
import SwarmLean.Lib.Report
import SwarmLean.Lib.Conflict
import SwarmLean.Lib.Workspaces
import SwarmLean.Spec.Data
import SwarmLean.Cmd.Hook
import HarnessRetro

/-! foundation_spec.lua's re asserts, and the patterns the CLI runs. -/

namespace SwarmLean.Test.Re
open SwarmLean.Re
open Lean (Json)

/-- The value of an `Except`, or the default. -/
def ok [Inhabited α] : Except String α → α
  | .ok a => a
  | .error _ => default

/-- re.findall's strings for a pattern with at most one group. -/
def fa (pat s : String) (fl : Flags := {}) : List String := (ok (findall pat s fl)).map (·.headD "")

#guard
  let m := (ok (search "(a)(x)?b" "zzab")).get!
  m.whole == "ab" && m.group 1 == some "a" && m.group 2 == none && m.s + 1 == 3
#guard (ok («match» "b" "ab")).isNone && ((ok («match» "a" "ab")).map (·.whole)) == some "a"
#guard (ok (fullmatch "(\\d+)([smh]?)" "12m")).isSome && (ok (fullmatch "(\\d+)([smh]?)" "12m\n")).isNone
#guard fa "\\w+|[^\\w\\s]|\\n" "héllo, wörld\n" == ["héllo", ",", "wörld", "\n"]
#guard fa "^worktree (.*)$" "worktree /a\nx\nworktree /b\n" M == ["/a", "/b"]
#guard ok (findall "(a)(b)?" "a ab") == [["a", ""], ["a", "b"]]
#guard
  let hunk := "^<<<<<<< .*?\\n(.*?)^\\|\\|\\|\\|\\|\\|\\| .*?\\n(.*?)^=======\\n(.*?)^>>>>>>> "
  let hs := ok (finditer hunk "x\n<<<<<<< o\nA\n||||||| b\nB\n=======\nC\n>>>>>>> t\n" (S.or M))
  hs.length == 1 && hs.map (fun h => [h.group 1, h.group 2, h.group 3]) == [[some "A\n", some "B\n", some "C\n"]]
#guard (fa "x*" "é").length == 2
-- harness-lint's hook-path token: lookbehind, positive and negative
#guard fa "(?:^|(?<=[\\s\"'=(]))(/[^\\s\"';|&]*)" "sh /a/b.sh x=/c 'q' y/d" == ["/a/b.sh", "/c"]
#guard fa "(?<!a)b" "ab cb" == ["b"] && (ok (search "(?<=ab)c" "abc")).map (·.s) == some 2
#guard ok (sub "[^\\w.-]" "_" "my repo/é") == "my_repo_é"
#guard escape "main red: run (1)" == "main\\ red\\:\\ run\\ \\(1\\)" && (ok («match» (escape "a.b") "axb")).isNone
#guard match compile "(unclosed" with | .error _ => true | .ok _ => false

/-- Every named literal pattern. -/
def PATS : List (String × Pat) :=
  [("Hook.PUSH", Cmd.Hook.PUSH), ("Hook.CD", Cmd.Hook.CD), ("Hook.SWARM_WAIT", Cmd.Hook.SWARM_WAIT),
   ("Workspaces.CHECKOUT", Workspaces.CHECKOUT), ("Conflict.TOK", Conflict.TOK), ("Run.RUN_DIR_RE", Run.RUN_DIR_RE),
   ("Report.SINCE", Report.SINCE), ("Hr.NON_ALNUM", HarnessRetro.NON_ALNUM),
   ("Transcript.REMINDER", HarnessRetro.Transcript.REMINDER), ("TimeReport.WAIT_LOOP", HarnessRetro.TimeReport.WAIT_LOOP),
   ("TimeReport.CI_WATCH", HarnessRetro.TimeReport.CI_WATCH), ("TimeReport.AGENT_BOLD", HarnessRetro.TimeReport.AGENT_BOLD),
   ("TimeReport.YOU_ARE", HarnessRetro.TimeReport.YOU_ARE), ("TimeReport.TOOL_USE_ID", HarnessRetro.TimeReport.TOOL_USE_ID),
   ("TimeReport.WAITING", HarnessRetro.TimeReport.WAITING), ("Lint.CODE", HarnessRetro.Lint.CODE),
   ("Lint.IMPORT", HarnessRetro.Lint.IMPORT), ("Lint.FRONT", HarnessRetro.Lint.FRONT), ("Lint.FIELD", HarnessRetro.Lint.FIELD),
   ("Lint.SKILL_SCRIPT", HarnessRetro.Lint.SKILL_SCRIPT), ("Lint.HOOK_PATH", HarnessRetro.Lint.HOOK_PATH),
   ("Lint.SCRIPT_PATH", HarnessRetro.Lint.SCRIPT_PATH), ("Probe.DENY", HarnessRetro.Probe.DENY)] ++
  HarnessRetro.TimeReport.KEYS.map fun (k, p) => (s!"TimeReport.KEYS {k}", p)

-- each parses (on failure: the names this lists), and one that does not is caught and matches nothing
#guard (PATS.filter (!·.2.parses)).map (·.1) == []
#guard !(Pat.lit "(unclosed").parses && ((Pat.lit "(unclosed").search "(unclosed").isNone

-- the CLI's own patterns (hook.lua, workspaces.lua, machine.lua)
#guard ((Cmd.Hook.PUSH.search "cd x && git -C /w push origin").bind (·.group 1)) == some "/w"
#guard (Cmd.Hook.PUSH.search "git pushy").isNone
#guard (Cmd.Hook.CD.findall "cd /a && (cd b; ls").map (·.headD "") == ["/a", "b"]
#guard ((Workspaces.CHECKOUT.search "git checkout -q main && x").bind (·.group 1)) == some "main"
#guard Cmd.Hook.SWARM_WAIT.test "swarm  wait --x" && !Cmd.Hook.SWARM_WAIT.test "swarm read"
#guard Run.runDirOk ".cache/swarm-run/repo/wt" && !Run.runDirOk "x/.cache/swarm-run/repo/wt" &&
  !Run.runDirOk ".cache/swarm-run/repo" && !Run.runDirOk ".cache/swarm-run/repo/wt\n"
#guard (Report.SINCE.search "2026-11-07T08:00").map (fun m => [m.group 1, m.group 4, m.group 6]) ==
  some [some "2026", some "08", some ""]
#guard (Report.SINCE.search "2026-11-07x").isNone
#guard (ok (fullmatch "(python[\\d.]*|node|bash|sh)" "python3.12")).isSome
#guard (ok (fullmatch (escape "ll-" ++ "(\\d+)") "ll-68")).bind (·.group 1) == some "68"
#guard ok (sub "b*" "-" "abc") == "-a--c-" && ok (sub "x*" "-" "abc") == "-a-b-c-"
#guard (ok (search "(?i)ABC" "xabc")).isSome && (ok (search "a{2,3}?" "aaaa")).map (·.whole) == some "aa"
#guard (ok (search "a(?=b)" "acab")).map (·.s) == some 2 && (ok (search "a(?!b)" "abac")).map (·.s) == some 2

-- HarnessRetro's text handling, pure
section
open HarnessRetro

/-- A JSON object of string fields. -/
def obj (kv : List (String × Json)) : Json := Json.mkObj kv

#guard TimeReport.key "Read" (obj []) == "Read"
#guard TimeReport.key "Bash" (obj [("command", .str "sleep 5; ls")]) == "bash: wait loop"
#guard TimeReport.key "Bash" (obj [("command", .str "gh run watch 12")]) == "gh: wait for CI"
#guard TimeReport.key "Bash" (obj [("command", .str "cd x && git status")]) == "git status"
#guard TimeReport.key "Bash" (obj [("command", .str "ls -la")]) == "bash: ls"
#guard TimeReport.label "You are gl-3, a swarm agent" "abcdefghij" == "gl-3"
#guard TimeReport.label "Brief for agent **w2** now" "abcdefghij" == "w2"
#guard TimeReport.label "the orchestrator" "abcdefghij" == "orchestrator"
#guard TimeReport.label "hello" "abcdefghij" == "abcdefgh"
#guard Transcript.clip "a<system-reminder>x\ny</system-reminder>b " 10 == "ab"
#guard Transcript.clip "abcdef" 3 == "abc …[3 more chars]"

-- a session: a brief, a foreground Bash call from 1 to 3, a background one from 4 whose notification comes at 9
#guard
  let tu (id cmd : String) (bg : Bool) : Json := obj [("type", .str "tool_use"), ("id", .str id), ("name", .str "Bash"),
    ("input", obj [("command", .str cmd), ("run_in_background", .bool bg)])]
  let tr (id : String) : Json := obj [("type", .str "tool_result"), ("tool_use_id", .str id)]
  let recs : Array TimeReport.Rec := #[
    { ty := "user", t := 0, c := some (.str "You are w1") },
    { ty := "assistant", t := 1, c := some (.arr #[tu "a" "git status" false]) },
    { ty := "user", t := 3, c := some (.arr #[tr "a"]) },
    { ty := "assistant", t := 4, c := some (.arr #[tu "b" "nix build" true]) },
    { ty := "user", t := 5, c := some (.arr #[tr "b"]) },
    { ty := "notify", t := 9, c := some (.str "<tool-use-id>b</tool-use-id> done") }]
  let t := TimeReport.tally #[("s1", recs)]
  t.tools.map (fun (k, r) => (k, r.total, r.count)) == #[("git status", 2.0, 1), ("nix build (bg)", 5.0, 1)] &&
    t.per == #[("w1", 2.0)] && t.model == #[("w1", 1.0)]

end

end SwarmLean.Test.Re
