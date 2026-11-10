#!/bin/sh
# Fresh random traces of swarm.qnt's `replay` instance, each replayed through the real CLI (cli_model_spec.lua).
# Usage: swarm/model/replay.sh [traces (20)] [steps (40)] [seed]. Needs nix (quint) and the swarm LuaJIT rocks.
here=$(cd "$(dirname "$0")" && pwd)
n=${1:-20} steps=${2:-40} seed=${3:-$(date +%s)}
out=$(mktemp -d) || exit 1
trap 'rm -rf "$out"' EXIT
nix shell nixpkgs#quint -c quint run --main replay --mbt --seed "$seed" --n-traces "$n" --max-samples "$n" \
  --max-steps "$steps" --out-itf "$out/seed$seed-{seq}.itf.json" "$here/swarm.qnt" >/dev/null || exit 1
echo "seed $seed: $(ls "$out" | wc -l) traces of up to $steps steps"
SWARM_MODEL_TRACES=$out luajit "$here/../lua/test/run.lua" cli_model
