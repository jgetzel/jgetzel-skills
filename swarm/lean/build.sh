#!/bin/sh
# Builds swarm-lean where swarm/swarm looks for it (and swarm-report, which swarm-retro/swarm-report runs, and
# Builds swarm-lean where swarm/swarm looks for it (and swarm-report, which swarm-retro/swarm-report runs,
# harness-retro, which harness-retro/hr.sh runs, and herdr-mods, which ../../herdr-mods/herdr-mods runs): with lake on
# PATH (elan), `lake build` here, then a touch, since lake leaves an up-to-date binary's mtime as it was and the
# launchers run only a binary newer than its sources; else with nix, the repo flake's swarm-lean package linked at
# .lake/nix (a new link each build).
cd "$(dirname "$0")" || exit 1
if command -v lake >/dev/null 2>&1; then
  lake build swarm-lean swarm-report harness-retro herdr-mods &&
    touch .lake/build/bin/swarm-lean .lake/build/bin/harness-retro .lake/build/bin/herdr-mods
elif command -v nix >/dev/null 2>&1; then
  mkdir -p .lake && nix build ../..#swarm-lean -o .lake/nix
else
  echo "swarm-lean needs lake (install elan: https://github.com/leanprover/elan) or nix" >&2; exit 1
fi || exit 1
# The hpl build, which the launcher runs first while it is newer than the sources: only where high-perf-lean has a
# compiler (or $HPL names one), as in check.sh. A failure leaves the stock binary above in use.
if [ -n "$HPL" ] || [ -x ../../../high-perf-lean/.lake/build/bin/hpl ]; then
  if command -v lake >/dev/null 2>&1; then (cd hpl && lake build); else (cd hpl && nix shell nixpkgs#elan -c lake build); fi \
    >.lake/hpl-build.log 2>&1 && touch hpl/.lake/build/bin/swarm-lean ||
    echo "swarm-lean: the hpl build failed (.lake/hpl-build.log); the stock binary stays in use" >&2
fi
