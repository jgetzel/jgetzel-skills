#!/bin/sh
# Builds claim where ./claim looks for it (and claim-tests, which check.sh runs): `lake build` here, with elan's lake on
# PATH, else the repo flake's pinned Lean through nix (.lake stays, so either builds only what changed), then a touch,
# since lake leaves an up-to-date binary's mtime as it was and the launcher runs only a binary newer than its sources.
cd -P "$(dirname "$0")" || exit 1
if command -v lake >/dev/null 2>&1; then lean=
elif command -v nix >/dev/null 2>&1; then lean="nix develop ..#lean -c"
else echo "claim needs lake (install elan: https://github.com/leanprover/elan) or nix" >&2; exit 1
fi
$lean lake build claim claim-tests && touch .lake/build/bin/claim
