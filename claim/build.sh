#!/bin/sh
# Builds claim where ./claim looks for it (and claim-tests, which check.sh runs): with lake on PATH (elan), `lake build`
# here, then a touch, since lake leaves an up-to-date binary's mtime as it was and the launcher runs only a binary newer
# than its sources; else with nix, the repo flake's claim package linked at .lake/nix (a new link each build).
cd -P "$(dirname "$0")" || exit 1
if command -v lake >/dev/null 2>&1; then
  lake build claim claim-tests && touch .lake/build/bin/claim
elif command -v nix >/dev/null 2>&1; then
  mkdir -p .lake && nix build ..#claim -o .lake/nix && touch .lake/nix.stamp
else
  echo "claim needs lake (install elan: https://github.com/leanprover/elan) or nix" >&2; exit 1
fi
