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
