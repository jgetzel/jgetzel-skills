#!/bin/sh
# Checks every theorem and counterexample of the model: builds it, and refuses a proof left open. Axioms: Lean's three,
# and the environment assumptions of SwarmModel/Env.lean, each tested by its own case in ../lua/test/env_spec.lua
# (sqlite's: sqlite_spec.lua)
# (Audit.lean prints which theorems rest on them, and fails on any other axiom).
# Needs lake (elan) on the PATH, or nix to fetch it.
cd "$(dirname "$0")" || exit 1
if grep -rnw 'sorry\|native_decide' SwarmModel; then echo "an open proof" >&2; exit 1; fi
if grep -rnw 'axiom' SwarmModel | grep -v '^SwarmModel/Env\.lean:'; then echo "an axiom outside Env.lean" >&2; exit 1; fi
for a in $(sed -n 's/^axiom \([A-Za-z0-9_]*\) :.*/\1/p' SwarmModel/Env.lean); do
  cat ../lua/test/env_spec.lua ../lua/test/sqlite_spec.lua | grep -qw "$a" ||
    { echo "Env.lean's $a has no case in env_spec.lua or sqlite_spec.lua" >&2; exit 1; }
done
lean_do() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
lean_do build && lean_do env lean Audit.lean
