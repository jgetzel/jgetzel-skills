#!/usr/bin/env bash
# The gate: total functions only (no partial def, no panicking access, no while/repeat loops, no sorry/unsafe/extern),
# both builds (stock Lean and hpl), the unit tests, and the differential tests against the real sqlite3.
set -uo pipefail
cd "$(dirname "$0")" || exit 1
fail=0
src="LSql/*.lean Main.lean"
# partial def and panicking access ([i]!, .get!, .head!, panic!, unreachable!...), outside comments and strings
perl ../swarm/lean/nopanic.pl $src || { echo "check: partial def or panicking access" >&2; fail=1; }
# while/repeat desugar to Loop.forIn, which is partial; sorry/unsafe/extern/implemented_by escape the type checker
if perl -0777 -ne 's{/-.*?-/}{}gs; s{--[^\n]*}{}g; s{"(?:\\.|[^"\\])*"}{""}g; print "$ARGV: $1\n" while /\b(while|repeat|sorry|admit|unsafe|implemented_by|extern|native_decide|set!)\b/g' $src | grep .; then
  echo "check: a forbidden construct (above)" >&2; fail=1
fi
lean_do() { nix develop "$HOME/workspace/high-perf-lean" -c "$@"; }
lean_do lake build lsqlite3 Tests LSqlProofs >/dev/null 2>.lake/check-build.log || { tail -20 .lake/check-build.log; echo "check: stock build (or a #guard, or a proof) failed" >&2; exit 1; }
# (pipefail: a failing diff.sh fails the pipeline, so the gate)
# the kernel's view: every LSql constant is a checked (terminating) definition, none partial/unsafe/opaque/extern
lean_do lake env lean Audit.lean || { echo "check: totality audit failed" >&2; fail=1; }
tests/diff.sh .lake/build/bin/lsqlite3 | tail -1 || fail=1
tests/diff.sh --file .lake/build/bin/lsqlite3 | tail -1 || fail=1
tests/compat.sh .lake/build/bin/lsqlite3 || fail=1
if [ -x hpl/.lake/build/bin/lsqlite3 ] || [ "${HPL_BUILD_CHECK:-1}" = 1 ]; then
  (cd hpl && lean_do lake build >../.lake/hpl-build.log 2>&1) \
    || { tail -20 .lake/hpl-build.log; echo "check: hpl build failed" >&2; exit 1; }
  echo "hpl refused: $(cat hpl/.lake/build/ir/hpl/*.refused 2>/dev/null | wc -l) functions (hpl/.lake/build/ir/hpl/*.refused)"
  tests/diff.sh hpl/.lake/build/bin/lsqlite3 | tail -1 || fail=1
  tests/diff.sh --file hpl/.lake/build/bin/lsqlite3 | tail -1 || fail=1
  tests/compat.sh hpl/.lake/build/bin/lsqlite3 || fail=1
fi
[ $fail = 0 ] && echo "check: ok"
exit $fail
