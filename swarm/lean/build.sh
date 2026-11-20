#!/bin/sh
# Builds swarm-lean where swarm/swarm looks for it (and swarm-report, which swarm-retro/swarm-report runs,
# harness-retro, which harness-retro/hr.sh runs, and herdr-mods, which ../../herdr-mods/herdr-mods runs): `lake build`
# here, with elan's lake on PATH, else the repo flake's pinned Lean through nix (.lake stays, so either builds only what
# changed), then a touch, since lake leaves an up-to-date binary's mtime as it was and the launchers run only a binary
# newer than its sources. The claim tool (../../claim) is built first by its own build.sh.
cd -P "$(dirname "$0")" || exit 1
# claim first: lake builds swarm-lean against ../../claim/.lake
../../claim/build.sh || exit 1
if command -v lake >/dev/null 2>&1; then lean=
elif command -v nix >/dev/null 2>&1; then lean="nix develop ../..#lean -c"
else echo "swarm-lean needs lake (install elan: https://github.com/leanprover/elan) or nix" >&2; exit 1
fi
$lean lake build swarm-lean swarm-report harness-retro herdr-mods &&
  touch .lake/build/bin/swarm-lean .lake/build/bin/harness-retro .lake/build/bin/herdr-mods
