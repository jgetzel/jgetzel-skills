#!/bin/sh
# Symlink every skill in this repo into ~/.claude/skills. Safe to re-run.
set -e
cd "$(dirname "$0")"
dest="$HOME/.claude/skills"
mkdir -p "$dest"
for skill in */SKILL.md; do
  name=${skill%/SKILL.md}
  if [ -e "$dest/$name" ] && [ ! -L "$dest/$name" ]; then
    echo "skipped $name: $dest/$name is a real directory, remove it and re-run" >&2
    continue
  fi
  ln -sfn "$PWD/$name" "$dest/$name"
  echo "linked $name"
done
# The swarm CLI is swarm-lean (swarm/lean), built with elan's lake or else nix; build.sh also builds swarm-report, harness-retro and herdr-mods.
swarm/lean/build.sh || echo "swarm: swarm-lean did not build; swarm/swarm says so until it does" >&2
# The Herdr Swarm and Calendar panels (herdr-mods/herdr-mods, a swarm-lean executable), when the Herdr desktop app is
# installed.
if [ -d "${HERDR_APP_HOME:-$HOME/.config/herdr-app}/mods/tabs" ]; then
  herdr-mods/herdr-mods install || echo "skipped the Herdr panels (see above)" >&2
fi
