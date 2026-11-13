#!/bin/sh
# Checks Store.lean's Atomic on the real store: 50 `task claim 1` processes at once under different names; exactly one
# prints success, and the file parses after. Usage: test-claim.sh [binary] (default: the stock build's).
B=$(realpath "${1:-$(dirname "$0")/.lake/build/bin/swarm-lean}") || exit 1
T=$(mktemp -d) || exit 1
export SWARM_LEAN_DB=$T/db.json
"$B" task add contested >/dev/null || exit 1
# each process spins until go exists, so all 50 start their transactions together
for k in $(seq 50); do
  (while [ ! -e "$T/go" ]; do :; done; SWARM_NAME=a$k exec "$B" task claim 1) >"$T/out$k" 2>&1 &
done
sleep 1; touch "$T/go"; wait
won=$(cat "$T"/out* | grep -cx claimed)
held=$(cat "$T"/out* | grep -c '^held by a')
board=$("$B" board) || { echo "FAIL: the store does not parse after: $(cat "$SWARM_LEAN_DB")"; exit 1; }
rm -r "$T"
echo "$won claimed, $held held; board: $board"
[ "$won" = 1 ] && [ "$held" = 49 ] && echo "$board" | grep -q '^#1 claimed a[0-9]* ' || { echo FAIL; exit 1; }
echo ok
