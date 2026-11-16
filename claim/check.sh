#!/bin/sh
# Builds claim and its tests, refuses an open proof or an axiom (Audit.lean), and runs claim-tests (the script's cases and
# claim's own, against a scratch ledger) on the built binary.
cd "$(dirname "$0")" || exit 1
if grep -rnw 'sorry\|admit\|native_decide\|^axiom' Claims Claims.lean Main.lean ClaimTests TestMain.lean; then echo "an open proof or an axiom" >&2; exit 1; fi
cmp -s lean-toolchain ../swarm/lean/lean-toolchain || { echo "claim/lean-toolchain differs from swarm/lean/lean-toolchain" >&2; exit 1; }
lean_do() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
lean_do build || exit 1
# Audit.lean prints every theorem's axioms and fails on any axiom but Lean's three
ax=$(lean_do env lean Audit.lean) || { echo "$ax"; exit 1; }
echo "$ax" | grep -v ": \[\(propext\|Classical.choice\|Quot.sound\|, \)*\]$"
echo "$ax" | grep -c "^'\?Claims" | sed 's/^/theorems audited: /'
.lake/build/bin/claim-tests >.lake/claim-tests.log 2>&1 || { grep -v "^ok " .lake/claim-tests.log; exit 1; }
tail -1 .lake/claim-tests.log
