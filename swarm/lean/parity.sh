#!/bin/sh
# The port's progress: runs the Lua CLI's cli_*_spec.lua tests against swarm-lean (SWARM_BIN, strict: no fall-through
# to Lua) and prints, per spec file, the tests passed, failed, and failed because a command is not ported (its error
# says "not ported: <cmd>", or swarm-lean left swarm-lean-not-ported in the test's kept fixture).
# Usage: parity.sh [--mixed] [binary] [pattern] (default: the stock build's binary; pattern: run.lua's, default cli_).
# --mixed: not strict, so an unported command runs the Lua CLI: every test should pass, each one checking the ported
# commands it runs against the Lua running the rest.
# Exits 1 when a test fails and no command it ran was unported; those are listed after the table, each with the head of
# its error.
cd "$(dirname "$0")" || exit 1
if [ "$1" = --mixed ]; then shift; export SWARM_LEAN_STRICT=0; fi
B=$(realpath "${1:-.lake/build/bin/swarm-lean}") || exit 1
[ -x "$B" ] || { echo "no binary $B: build first" >&2; exit 1; }
T=$(mktemp -d) || exit 1
mkdir "$T/tmp"
# the fixtures of failed tests are kept: in $T/tmp, removed below
TMPDIR=$T/tmp SWARM_BIN=$B luajit ../lua/test/run.lua "${2:-cli_}" >"$T/out"
awk -v T="$T" '
  function flush() {
    if (cur == "") return
    if (np) n[cur]++; else { f[cur]++; printf "  %s %s\n%s", cur, test, why >> (T "/fails") }
    cur = ""
  }
  /^ok    / { flush(); split($0, a, " "); p[a[2]]++; files[a[2]] = 1; next }
  /^FAIL  / { flush(); cur = substr($0, 7); sub(/ .*/, "", cur); test = substr($0, 7 + length(cur) + 1); files[cur] = 1; np = 0; why = ""; nw = 0; next }
  /^[0-9]+ run, [0-9]+ failed$/ { flush(); next }
  /not ported: / { if (cur != "") np = 1 }
  /\(fixture kept: / {
    d = $0; sub(/.*\(fixture kept: /, "", d); sub(/\).*/, "", d)
    if (cur != "" && system("test -e \"" d "/swarm-lean-not-ported\"") == 0) np = 1
  }
  cur != "" && nw++ < 12 { why = why "    " $0 "\n" }  # the failure, for a log with no other trace of it (CI)
  END {
    flush()
    for (k in files) { printf "%-28s %6d %6d %10d\n", k, p[k], f[k], n[k] > (T "/rows"); tp += p[k]; tf += f[k]; tn += n[k] }
    printf "%-28s %6d %6d %10d\n", "total", tp, tf, tn > (T "/total")
  }' "$T/out"
printf "%-28s %6s %6s %10s\n" spec passed failed not-ported
sort "$T/rows"
cat "$T/total"
rc=0
if [ -s "$T/fails" ]; then echo "failed, not for a missing port:"; cat "$T/fails"; rc=1; fi
rm -rf "$T"
exit $rc
