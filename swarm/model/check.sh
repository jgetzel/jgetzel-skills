#!/bin/sh
# Checks every theorem and counterexample of the model: builds it, and refuses a proof left open.
# Needs lake (elan) on the PATH, or nix to fetch it.
cd "$(dirname "$0")" || exit 1
if grep -rnw 'sorry\|native_decide\|axiom' SwarmModel; then echo "an open proof, or an axiom" >&2; exit 1; fi
if command -v lake >/dev/null; then lake build; else nix shell nixpkgs#elan -c lake build; fi
