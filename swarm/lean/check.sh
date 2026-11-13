#!/bin/sh
# Builds swarm-lean and its proofs, refuses an open proof or an axiom beyond Lean's three, and on the stock binary and
# the hpl one (when ../../../high-perf-lean has an hpl binary, or $HPL is set) runs parity.sh, strict and --mixed,
# and test-claim.sh.
cd "$(dirname "$0")" || exit 1
if grep -rnw 'sorry\|admit\|native_decide\|^axiom' SwarmLean Main.lean; then echo "an open proof or an axiom" >&2; exit 1; fi
lean_do() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
lean_do build || exit 1
ax=$(lean_do env lean Audit.lean) || exit 1
echo "$ax"
[ "$(echo "$ax" | grep -c "^'SwarmLean")" = 5 ] || { echo "Audit.lean printed no axioms for some theorem" >&2; exit 1; }
if echo "$ax" | sed -n 's/.*axioms: \[\(.*\)\]/\1/p' | tr ',' '\n' | tr -d ' ' | grep -v '^\(propext\|Classical.choice\|Quot.sound\)$'; then
  echo "an axiom beyond Lean's three" >&2; exit 1
fi
on() { ./parity.sh "$1" && ./parity.sh --mixed "$1" && ./test-claim.sh "$1"; }
on .lake/build/bin/swarm-lean || exit 1
if [ -n "$HPL" ] || [ -x ../../../high-perf-lean/.lake/build/bin/hpl ]; then
  (cd hpl && lean_do build) || exit 1
  cat hpl/.lake/build/ir/hpl/*.refused 2>/dev/null | cut -f2,4 | sed 's/^/hpl refused: /'
  on hpl/.lake/build/bin/swarm-lean || exit 1
else echo "no hpl binary: skipped the hpl build"; fi
