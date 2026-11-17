#!/bin/sh
# Builds swarm-lean where swarm/swarm looks for it (and swarm-report, which swarm-retro/swarm-report runs, and
# Builds swarm-lean where swarm/swarm looks for it (and swarm-report, which swarm-retro/swarm-report runs,
# harness-retro, which harness-retro/hr.sh runs, and herdr-mods, which ../../herdr-mods/herdr-mods runs): with lake on
# PATH (elan), `lake build` here, then a touch, since lake leaves an up-to-date binary's mtime as it was and the
# launchers run only a binary newer than its sources; else with nix, the repo flake's swarm-lean package linked at
# .lake/nix (a new link each build). The claim tool (../../claim) is built first by its own build.sh.
# -P: run through the ~/.claude/skills/swarm link, a logical cd would resolve ../../claim beside the link
cd -P "$(dirname "$0")" || exit 1
# claim first: lake builds swarm-lean against ../../claim/.lake
../../claim/build.sh || exit 1
if command -v lake >/dev/null 2>&1; then
  lake build swarm-lean swarm-report harness-retro herdr-mods &&
    touch .lake/build/bin/swarm-lean .lake/build/bin/harness-retro .lake/build/bin/herdr-mods
elif command -v nix >/dev/null 2>&1; then
  mkdir -p .lake && nix build ../..#swarm-lean -o .lake/nix && touch .lake/nix.stamp
else
  echo "swarm-lean needs lake (install elan: https://github.com/leanprover/elan) or nix" >&2; exit 1
fi
