#!/bin/sh
# Fresh random runs of the Lean model's `replay` instance, each replayed through the real CLI (cli_model_spec.lua);
# first, fresh random lock patterns checked against locks.lua (GlobCases.lean, locks_model_spec.lua), and fresh random
# Lua chunks run by the Lean semantics of our Lua subset and by LuaJIT (LuaCases.lean, luasem_spec.lua).
# Usage: swarm/model/replay.sh [traces (20)] [steps (40)] [seed]. Needs lake (elan), or nix to fetch it, and the
# swarm LuaJIT rocks. KEEP=<dir> keeps the traces there.
here=$(cd "$(dirname "$0")" && pwd)
n=${1:-20} steps=${2:-40} seed=${3:-$(date +%s)}
out=${KEEP:-$(mktemp -d)} || exit 1
g=$(mktemp) || exit 1
l=$(mktemp) || exit 1
trap 'rm -f "$g" "$l"; [ -n "$KEEP" ] || rm -rf "$out"' EXIT
lean() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
"$here/gen-lock-src.sh" --check || exit 1
(cd "$here" && lean build >/dev/null && lean env lean --run SwarmModel/Traces.lean "$n" "$steps" "$seed" "$out") || exit 1
(cd "$here" && lean env lean --run SwarmModel/GlobCases.lean 3000 "$seed" true "$g") || exit 1
SWARM_MODEL_GLOBS=$g luajit "$here/../lua/test/run.lua" locks_model || exit 1
(cd "$here" && lean env lean --run SwarmModel/LuaCases.lean 3000 "$seed" "$l") || exit 1
SWARM_LUASEM_CASES=$l luajit "$here/../lua/test/run.lua" luasem || exit 1
echo "seed $seed: $(ls "$out" | wc -l) traces of up to $steps steps"
SWARM_MODEL_TRACES=$out luajit "$here/../lua/test/run.lua" cli_model
