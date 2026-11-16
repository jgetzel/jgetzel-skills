import ClaimTests.Script
import ClaimTests.Cli
import ClaimTests.Ledger
import ClaimTests.Spec

/-! claim-tests: `claim-tests [pattern]` runs every test whose spec or name contains the pattern, one after another, each
in a fresh scratch dir; `--list` prints `spec name` per test (check.sh ties an assumption's tag to a case). -/

open Claims Claims.Tests

/-- Every test: the spec (a group), the name and the body. -/
def all : List (String × String × (T → IO Unit)) :=
  [("script_spec", Script.tests), ("cli_spec", Cli.tests), ("claims_spec", Spec.tests)].flatMap fun (s, cs) => cs.map fun (n, f) => (s, n, f)

def main (args : List String) : IO UInt32 := do
  if args == ["--list"] then
    for (s, n, _) in all do IO.println s!"{s} {n}"
    return 0
  let pat := args.head?
  let mut failed := 0
  let mut ran := 0
  for (s, n, f) in all do
    if pat.all fun p => subIn s p || subIn n p then
      ran := ran + 1
      let t ← T.new
      let err ← try f t; pure none catch e => pure (some (toString e))
      t.cleanup err.isNone
      match err with
      | none => IO.println s!"ok    {s} {n}"
      | some e => failed := failed + 1; IO.println s!"FAIL  {s} {n}\n{e}\n  (fixture kept: {t.d})"
  IO.println s!"{ran - failed} of {ran} passed"
  return if failed == 0 then 0 else 1
