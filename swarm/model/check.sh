#!/bin/sh
# Checks every theorem and counterexample of the model: builds it, and refuses a proof left open. Axioms: Lean's three
# only (board #68): what the model trusts about the world is a hypothesis of SwarmModel/Env.lean, each tested by the
# case its tag names in ../lua/test/env_spec.lua or sqlite_spec.lua (Audit.lean prints which theorems take which, and
# fails on any other axiom or an untagged hypothesis). Then example/Client.lean, a proof downstream of
# SwarmModel/Contract.lean.
# Needs lake (elan) on the PATH, or nix to fetch it.
cd "$(dirname "$0")" || exit 1
if grep -rnw 'sorry\|native_decide' SwarmModel example; then echo "an open proof" >&2; exit 1; fi
if grep -rnw '^axiom\|^opaque' SwarmModel example; then echo "an axiom: assume it as a hypothesis (Env.lean)" >&2; exit 1; fi
for a in $(sed -n 's/.*(\(env\|sqlite\)_spec: \([a-z0-9_]*\)).*/\2/p' SwarmModel/Env.lean); do
  cat ../lua/test/env_spec.lua ../lua/test/sqlite_spec.lua | grep -qw "$a" ||
    { echo "Env.lean's $a has no case in env_spec.lua or sqlite_spec.lua" >&2; exit 1; }
done
lean_do() { if command -v lake >/dev/null; then lake "$@"; else nix shell nixpkgs#elan -c lake "$@"; fi; }
lean_do build && lean_do env lean Audit.lean && lean_do env lean example/Client.lean
