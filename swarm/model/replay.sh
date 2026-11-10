#!/bin/sh
# Fresh random runs of the Lean model's `replay` instance, each replayed through the real CLI (cli_model_spec.lua).
# Usage: swarm/model/replay.sh [traces (20)] [steps (40)] [seed]. Needs lake (elan), or nix to fetch it, and the
# swarm LuaJIT rocks. KEEP=<dir> keeps the traces there.
here=$(cd "$(dirname "$0")" && pwd)
n=${1:-20} steps=${2:-40} seed=${3:-$(date +%s)}
out=${KEEP:-$(mktemp -d)} || exit 1
[ -n "$KEEP" ] || trap 'rm -rf "$out"' EXIT
lean() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
(cd "$here" && lean build >/dev/null && lean env lean --run SwarmModel/Traces.lean "$n" "$steps" "$seed" "$out") || exit 1
echo "seed $seed: $(ls "$out" | wc -l) traces of up to $steps steps"
SWARM_MODEL_TRACES=$out luajit "$here/../lua/test/run.lua" cli_model
