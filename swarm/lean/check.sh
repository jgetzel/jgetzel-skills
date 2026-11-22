#!/bin/sh
# Builds swarm-lean and its proofs, refuses an open proof or an axiom beyond Lean's three (Audit.lean), checks the layering
# (layering.sh) and Challenge.lean against the proofs by Comparator (challenge.sh), and on the stock binary and
# the hpl one (when ../../../high-perf-lean has an hpl binary, or $HPL is set) runs swarm-tests (the Lean suite) and
# test-claim.sh; and harness-retro's test (test-harness-retro.sh). The claim tool's own gate (../../claim/check.sh) runs first.
cd "$(dirname "$0")" || exit 1
# the claim tool's own gate (../../claim: its proofs' axioms and claim-tests) first, and both toolchains the same
../../claim/check.sh || exit 1
cmp -s lean-toolchain ../../claim/lean-toolchain || { echo "swarm/lean/lean-toolchain differs from claim/lean-toolchain" >&2; exit 1; }
# Challenge.lean's sorries are its statements and holes (challenge.sh checks they are its only diagnostics)
if grep -rnw --exclude=Challenge.lean 'sorry\|admit\|native_decide\|^axiom' SwarmLean Main.lean HarnessRetro HarnessRetroMain.lean; then echo "an open proof or an axiom" >&2; exit 1; fi
# the spec layer imports no proof and no implementation; nothing but the proofs imports a proof (board #216)
./layering.sh || exit 1
# git runs only through Git.git / Git.out (World.lean: they put `--end-of-options` before ref operands), never a raw argv
if grep -rn 'Proc\.output (\?\["git"' SwarmLean Main.lean | grep -v '^SwarmLean/World.lean:'; then echo "a raw Proc.output [\"git\" outside World.lean" >&2; exit 1; fi
# a signal is sent only by the orphan sweep (to Watchd.orphanVictims), the takeover of a stale watchd, and hc kill
if grep -rn '"kill"' SwarmLean Main.lean HarnessRetro HarnessRetroMain.lean | grep -v '"hc", "kill"\|^SwarmLean/Assumptions.lean\|-- kill-site:'; then
  echo "a kill outside the orphan sweep and hc kill" >&2; exit 1
fi
lean_do() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
lean_do build || exit 1
# The proofs are out of the build until sw-global's proofs phase (board #79-#82; SwarmLean/Proofs/LEGACY.md): Audit.lean
# (which imports them) and challenge.sh come back with them.
if [ -n "$SWARM_PROOFS" ]; then
# Audit.lean prints every theorem's axioms and the theorems taking each assumption, and fails on any axiom but Lean's three
ax=$(lean_do env lean Audit.lean) || { echo "$ax"; exit 1; }
echo "$ax" | grep -v ": \[\(propext\|Classical.choice\|Quot.sound\|, \)*\]$"
echo "$ax" | grep -c "^'\?Swarm" | sed 's/^/theorems audited: /'
# each assumption's tag names a case of swarm-tests' env_spec or sqlite_spec, which checks it against the real tool (a
# tag may wrap a line)
cases=$(.lake/build/bin/swarm-tests --list) || exit 1
tags=$(cat SwarmLean/Assumptions.lean SwarmLean/Assumptions/Code.lean | tr '\n' ' ' | grep -o '(\(env\|sqlite\)_spec: [a-z0-9_, ]*)' | tr -d '(),:')
[ -n "$tags" ] || { echo "Assumptions.lean has no (env_spec: …) tag" >&2; exit 1; }
echo "$tags" | while read -r spec names; do
  for a in $names; do
    echo "$cases" | grep -qx "$spec $a" || { echo "Assumptions.lean's $a has no case in swarm-tests' $spec" >&2; exit 1; }
  done
done || exit 1
# Challenge.lean against the proofs, by Comparator, and its two mutants rejected (board #216)
./challenge.sh || exit 1
fi
on() { SWARM_BIN=$(realpath "$1") .lake/build/bin/swarm-tests >.lake/swarm-tests.log 2>&1 || { grep -v "^ok " .lake/swarm-tests.log; return 1; }; tail -1 .lake/swarm-tests.log; ./test-claim.sh "$1"; }
on .lake/build/bin/swarm-lean || exit 1
./test-harness-retro.sh || exit 1
if [ -n "$HPL" ] || [ -x ../../../high-perf-lean/.lake/build/bin/hpl ]; then
  # hpl notes every box it makes: the log keeps them, a failure shows its tail
  (cd hpl && lean_do build >../.lake/hpl-build.log 2>&1) || { tail -40 .lake/hpl-build.log; exit 1; }
  cat hpl/.lake/build/ir/hpl/*.refused 2>/dev/null | cut -f2,4 | sed 's/^/hpl refused: /'
  on hpl/.lake/build/bin/swarm-lean || exit 1
else echo "no hpl binary: skipped the hpl build"; fi
