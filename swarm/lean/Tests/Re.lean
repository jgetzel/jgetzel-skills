import SwarmLean.Lib.Re

/-! foundation_spec.lua's re asserts, and the patterns the CLI runs. -/

namespace SwarmLean.Test.Re
open SwarmLean.Re

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
#guard ok (sub "[^\\w.-]" "_" "my repo/é") == "my_repo_é"
#guard escape "main red: run (1)" == "main\\ red\\:\\ run\\ \\(1\\)" && (ok («match» (escape "a.b") "axb")).isNone
#guard match compile "(unclosed" with | .error _ => true | .ok _ => false

-- the CLI's own patterns (hook.lua, workspaces.lua, machine.lua)
#guard ((ok (search "\\bgit\\s+(?:-C\\s+(\\S+)\\s+)?push\\b" "cd x && git -C /w push origin")).bind (·.group 1)) == some "/w"
#guard (ok (search "\\bgit\\s+(?:-C\\s+(\\S+)\\s+)?push\\b" "git pushy")).isNone
#guard fa "(?:^|[;&|(]\\s*)cd\\s+([^\\s;&|)]+)" "cd /a && (cd b; ls" == ["/a", "b"]
#guard ((ok (search "\\bgit\\s+(?:checkout|switch)\\s+(?:-[qf]\\s+)*([^\\s;&|-][^\\s;&|]*)\\s*(?:$|[;&|])"
  "git checkout -q main && x")).bind (·.group 1)) == some "main"
#guard (ok (fullmatch "(python[\\d.]*|node|bash|sh)" "python3.12")).isSome
#guard (ok (fullmatch (escape "ll-" ++ "(\\d+)") "ll-68")).bind (·.group 1) == some "68"
#guard ok (sub "b*" "-" "abc") == "-a--c-" && ok (sub "x*" "-" "abc") == "-a-b-c-"
#guard (ok (search "(?i)ABC" "xabc")).isSome && (ok (search "a{2,3}?" "aaaa")).map (·.whole) == some "aa"
#guard (ok (search "a(?=b)" "acab")).map (·.s) == some 2 && (ok (search "a(?!b)" "abac")).map (·.s) == some 2

end SwarmLean.Test.Re
