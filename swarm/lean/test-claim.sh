#!/bin/sh
# Checks Store.lean's Atomic on the real store: 50 `task claim 1` processes at once under different names, on one
# SQLite db; exactly one succeeds, the rest are refused as held, and the db reads after.
# Usage: test-claim.sh [binary] (default: the stock build's).
B=$(realpath "${1:-$(dirname "$0")/.lake/build/bin/swarm-lean}") || exit 1
T=$(mktemp -d) || exit 1
export SWARM_DB=$T/swarm.db
# the scratch db's one swarm, of this repo (sw-global §2); every command after acts on it
env -u SWARM -u SWARM_NAME "$B" new t --repo . >/dev/null || exit 1
export SWARM=t
# the user files it: an agent's task would be Proposed, which a claim refuses
SWARM_NAME=human "$B" task add contested >/dev/null || exit 1
# each process spins until go exists, so all 50 start their transactions together
for k in $(seq 50); do
  (while [ ! -e "$T/go" ]; do :; done; SWARM_NAME=a$k exec "$B" task claim 1) >"$T/out$k" 2>&1 &
done
sleep 1; touch "$T/go"; wait
won=$(cat "$T"/out* | grep -c '^claimed #1 until ')
held=$(cat "$T"/out* | grep -c '^swarm: task #1 is In Progress, owned by a[0-9]*$')
board=$("$B" board) || { echo "FAIL: the db does not read after"; exit 1; }
rm -r "$T"
echo "$won claimed, $held held"
[ "$won" = 1 ] && [ "$held" = 49 ] && echo "$board" | grep -q '^#1 In Progress a[0-9]* ' || { echo "FAIL: $board"; exit 1; }
echo ok
