#!/bin/sh
# Claims for the System section's Compute card (board #189), inside shot.sh's sandbox after rail-demo.sh:
#   swarm/herdr/shot.sh --rework real --before 'sh swarm/herdr/compute-demo.sh none|claims|off; herdr-app do rw-bar.system' out.png
# none: empty ledgers. claims: this computer runs two jobs; desktop (16 cores, 15 busy) three under a cap of 14 cores,
# with a waiter unclaimed use holds back and one the cap holds back. off: claims, then desktop turned off. Claims hold for an hour (holder t);
# waiters' tickets go stale a minute after this runs.
set -eu
[ -n "${HERDR_APP_HOME:-}" ] && case $HERDR_APP_HOME in /tmp/hs.*) ;; *) false ;; esac ||
  { echo "compute-demo.sh: only inside shot.sh's sandbox" >&2; exit 2; }
here=${XDG_STATE_HOME:-$HOME/.local/state}/swarm-compute desk=$(dirname "$HERDR_APP_HOME")/w/desktop/compute
case ${1:-} in none|claims|off) ;; *) echo "compute-demo.sh: none, claims or off" >&2; exit 2 ;; esac
for d in "$here" "$desk"; do rm -rf "$d"; mkdir -p "$d/claims" "$d/queue"; done
[ "$1" != none ] || exit 0
now=$(date +%s) g=1048576
claim() { echo "$3 $(($4 * g)) t$((now + 3600)) $((now - $5)) $2 $6" >"$1/claims/$2-$5"; } # claim <ledger> <who> <cores> <G> <age s> <cmd>
wait_() { echo "$((now - $5)) $3 $(($4 * g)) $2" >"$1/queue/$2-w"; } # wait_ <ledger> <who> <cores> <G> <age s>
claim "$here" ll-97 4 6 1260 'nix shell nixpkgs#elan -c lake build SwarmLean'
claim "$here" ll-110 2 2 300 'node swarm/herdr/rail-fuzz.mjs'
claim "$desk" ll-203 6 12 2700 'cargo build --release -p hpl-core'
claim "$desk" ll-205 2 4 840 'cargo test -p hpl-parse'
claim "$desk" hpl-4 2 3 60 'lake build HplBench'
echo "14 -" >"$desk/cap"
wait_ "$desk" ll-111 4 4 130 # 3 free: 15 busy less 10 claimed less 2 of noise takes 3 of the cap's 4
wait_ "$desk" ll-209 6 8 45 # 10 of 14 claimed: the cap
[ "$1" != off ] || : >"$desk/off"
