import Tests.Cli.Fixture

/-! foundation_spec.lua's proc asserts, on the Lean's process calls (`execIO'`, which is Sys.exec and the fixture's
t.exec, and `outputIO`, Proc.output). -/

namespace SwarmLean.Tests.Spec.Foundation
open SwarmLean SwarmLean.Tests.Cli
open Lean (Json toJson)

def test_proc (_ : T) : IO Unit := do
  let r ← execIO' ["sh", "-c", "cat; echo err >&2; pwd; echo \"$FOO\"; exit 3"]
    { input := some "in\n", cwd := some "/", env := [("FOO", some "bar")] }
  eq r.stdout "in\n/\nbar\n"; eq r.stderr "err\n"; eq r.code.toNat 3
  let big := String.ofList (List.replicate 300000 'x')
  -- 300 KB in, out and on stderr at once: no deadlock
  eq (← execIO' ["sh", "-c", "cat; head -c 300000 /dev/zero >&2"] { input := some big }).stdout big
  eq (← execIO' ["no-such-binary-xyz"] {}).code.toNat 127
  -- a child that never reads its stdin
  eq (← execIO' ["true"] { input := some big }).code.toNat 0
  eq ((← outputIO ["false"] none []).map (·.code.toNat)) (some 1)
  eq ((← outputIO ["echo", "hi"] none []).map (·.stdout)) (some "hi\n")
  has (((← outputIO ["git", "--version"] none []).map (·.stdout)).getD "") "git version"
  eq (← execIO' ["sh", "-c", "echo out; echo err >&2"] { merge := true }).stdout "out\nerr\n"

def tests : List Case := [("test_proc", test_proc)]

end SwarmLean.Tests.Spec.Foundation
