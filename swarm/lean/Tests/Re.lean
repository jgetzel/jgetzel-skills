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

/-! The matcher before it took fuel, kept as the oracle the fuelled one must answer like. -/
namespace Oracle

mutual

/-- Matches `n` at `i` and then the continuation `k`. -/
partial def go (s : Array Char) (n : Node) (i : Nat) (caps : Caps) (k : Nat → Caps → R) : R :=
  let at? := s[i]?
  let prev := if i == 0 then none else s[i - 1]?
  match n with
  | .ch c ci => match at? with
    | some x => if x == c || (ci && low x == low c) then k (i + 1) caps else none
    | none => none
  | .any dotall => match at? with
    | some x => if dotall || x != '\n' then k (i + 1) caps else none
    | none => none
  | .cls neg items ci => match at? with
    | some x =>
      let hit := items.any (·.has x) || (ci && (items.any (·.has (low x)) || items.any (·.has x.toUpper)))
      if hit != neg then k (i + 1) caps else none
    | none => none
  | .bol multi => if i == 0 || (multi && prev == some '\n' && i < s.size) then k i caps else none
  | .eol multi =>
    if i == s.size || (multi && at? == some '\n') || (i + 1 == s.size && at? == some '\n') then k i caps else none
  | .bos => if i == 0 then k i caps else none
  | .eos => if i == s.size then k i caps else none
  | .eosNl => if i == s.size || (i + 1 == s.size && at? == some '\n') then k i caps else none
  | .wordB neg =>
    let b := (prev.map isWord).getD false != (at?.map isWord).getD false
    if b != neg then k i caps else none
  | .group idx body => go s body i caps fun j c => k j (match idx with | some g => c.set! g (some (i, j)) | none => c)
  | .look neg body =>
    match go s body i caps fun j c => some (j, c) with
    | some (_, c) => if neg then none else k i c
    | none => if neg then k i caps else none
  | .lookB neg body =>
    match goBack s body i i caps with
    | some (_, c) => if neg then none else k i c
    | none => if neg then k i caps else none
  | .cat ns => goSeq s ns i caps k
  | .alt ns => goAlt s ns i caps k
  | .rep body lo hi greedy => goRep s body lo hi greedy 0 i caps k

/-- Matches the nodes one after another. -/
partial def goSeq (s : Array Char) (ns : List Node) (i : Nat) (caps : Caps) (k : Nat → Caps → R) : R :=
  match ns with
  | [] => k i caps
  | n :: rest => go s n i caps fun j c => goSeq s rest j c k

/-- Tries the alternatives in order. -/
partial def goAlt (s : Array Char) (ns : List Node) (i : Nat) (caps : Caps) (k : Nat → Caps → R) : R :=
  match ns with
  | [] => none
  | n :: rest => match go s n i caps k with
    | some r => some r
    | none => goAlt s rest i caps k

/-- A match of `body` from `start` or an earlier start (nearest first) that ends exactly at `i`: a lookbehind. -/
partial def goBack (s : Array Char) (body : Node) (i start : Nat) (caps : Caps) : R :=
  match go s body start caps fun j c => if j == i then some (j, c) else none with
  | some r => some r
  | none => if start == 0 then none else goBack s body i (start - 1) caps

/-- `count` repetitions done; an iteration past the minimum that matches empty ends the loop. -/
partial def goRep (s : Array Char) (body : Node) (lo : Nat) (hi : Option Nat) (greedy : Bool) (count i : Nat)
    (caps : Caps) (k : Nat → Caps → R) : R :=
  let more : Unit → R := fun _ =>
    go s body i caps fun j c => if j == i && count ≥ lo then none else goRep s body lo hi greedy (count + 1) j c k
  if count < lo then more ()
  else if hi.any (count ≥ ·) then k i caps
  else if greedy then match more () with
    | some r => some r
    | none => k i caps
  else match k i caps with
    | some r => some r
    | none => more ()

end

/-- The first match starting at or after `init`, by the oracle. -/
def exec (r : Regex) (s : Array Char) (init : Nat := 0) : Option Match := Id.run do
  for st in [init:s.size + 1] do
    if let some (e, c) := go s r.root st (Array.replicate (r.groups + 1) none) fun j c => some (j, c) then
      return some { s := st, e, whole := slice s st e,
                    groups := (List.range r.groups).toArray.map fun g => c[g + 1]!.map fun (a, b) => slice s a b }
  return none

end Oracle

/-- Subjects for the comparison: the CLI's kinds of text, and runs that make the patterns below backtrack. -/
def SUBJECTS : List String :=
  ["", "a", "\n", "cd /a && git -C /w push origin main", "git checkout -q main && x", "worktree /a\nx\nworktree /b\n",
   "<system-reminder>x\ny</system-reminder> b", "2026-11-07T08:00", "sh /a/b.sh x=/c 'q' y/d", "@~/x.md and @y\n",
   "python3 ~/.claude/skills/a/b.py", "héllo, wörld\n", "aaaaaaaaaaaa", "aaaaaaaaaaab", "ababababc", "abcabc\n\n"]

/-- Patterns that backtrack hard, nest repetitions or look around. -/
def HARD : List String :=
  ["(a*)*b", "(a|aa)*c", "(?:a?){12}a{12}", "((a?){3}){3}b", "(?<=(?:a|b)+)c", "((a|b)*?c)+", "(?!(?:a*)*b)a",
   "(?<!a{2})b", "^(\\w+\\s?)*$", "(x+x+)+y", "(?:(?=(a+))a)*b", "\\b\\w+\\b", "(?m)^$", "(?s).*?\\n\\n"]

/-- Whether both matchers answer alike from every start in `s`. -/
def same (r : Regex) (s : String) : Bool :=
  let cs := s.toList.toArray
  let key (m : Option Match) := m.map fun m => (m.s, m.e, m.groups)
  (List.range (cs.size + 1)).all fun i => key (exec r cs i) == key (Oracle.exec r cs i)

#guard (PATS.filter fun (_, p) => !SUBJECTS.all (same p.re ·)).map (·.1) == []
#guard HARD.all fun p => (compile p).toOption.isSome
#guard (HARD.filter fun p => !SUBJECTS.all (same (ok (compile p)) ·)) == []
-- fuel: `exec`'s default is never spent; given less, a branch out of fuel fails, and here the whole match
#guard
  let r := ok (compile "a{30}")
  let s := (String.ofList (List.replicate 30 'a')).toList.toArray
  (exec r s).isSome && (exec r s 0 10).isNone
-- the parser's fuel: 400 nested groups parse
#guard (compile (String.ofList (List.replicate 400 '(') ++ "a" ++ String.ofList (List.replicate 400 ')'))).toOption.isSome

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
