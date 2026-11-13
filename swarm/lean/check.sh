#!/bin/sh
# Builds swarm-lean and its proofs, refuses an open proof or an axiom beyond Lean's three (Audit.lean), and on the stock binary and
# the hpl one (when ../../../high-perf-lean has an hpl binary, or $HPL is set) runs swarm-tests (the Lean suite) and
# test-claim.sh; and harness-retro's test (test-harness-retro.sh).
cd "$(dirname "$0")" || exit 1
if grep -rnw 'sorry\|admit\|native_decide\|^axiom' SwarmLean Main.lean HarnessRetro HarnessRetroMain.lean; then echo "an open proof or an axiom" >&2; exit 1; fi
lean_do() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
lean_do build || exit 1
# Audit.lean prints every theorem's axioms and the theorems taking each assumption, and fails on any axiom but Lean's three
ax=$(lean_do env lean Audit.lean) || { echo "$ax"; exit 1; }
echo "$ax" | grep -v ": \[\(propext\|Classical.choice\|Quot.sound\|, \)*\]$"
echo "$ax" | grep -c "^'\?Swarm" | sed 's/^/theorems audited: /'
# each assumption's tag names a case of swarm-tests' env_spec or sqlite_spec, which checks it against the real tool (a
# tag may wrap a line)
cases=$(.lake/build/bin/swarm-tests --list) || exit 1
tags=$(tr '\n' ' ' <SwarmLean/Assumptions.lean | grep -o '(\(env\|sqlite\)_spec: [a-z0-9_, ]*)' | tr -d '(),:')
[ -n "$tags" ] || { echo "Assumptions.lean has no (env_spec: …) tag" >&2; exit 1; }
echo "$tags" | while read -r spec names; do
  for a in $names; do
    echo "$cases" | grep -qx "$spec $a" || { echo "Assumptions.lean's $a has no case in swarm-tests' $spec" >&2; exit 1; }
  done
done || exit 1
on() { SWARM_BIN=$(realpath "$1") .lake/build/bin/swarm-tests >.lake/swarm-tests.log 2>&1 || { grep -v "^ok " .lake/swarm-tests.log; return 1; }; tail -1 .lake/swarm-tests.log; ./test-claim.sh "$1"; }
on .lake/build/bin/swarm-lean || exit 1
./test-harness-retro.sh || exit 1
if [ -n "$HPL" ] || [ -x ../../../high-perf-lean/.lake/build/bin/hpl ]; then
  # hpl notes every box it makes: the log keeps them, a failure shows its tail
  (cd hpl && lean_do build >../.lake/hpl-build.log 2>&1) || { tail -40 .lake/hpl-build.log; exit 1; }
  cat hpl/.lake/build/ir/hpl/*.refused 2>/dev/null | cut -f2,4 | sed 's/^/hpl refused: /'
  on hpl/.lake/build/bin/swarm-lean || exit 1
else echo "no hpl binary: skipped the hpl build"; fi
