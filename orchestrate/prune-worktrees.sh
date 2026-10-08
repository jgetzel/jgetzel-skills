#!/usr/bin/env bash
# Remove worktrees under .worktrees/ whose branch's PR is merged and which have
# no uncommitted changes. Dry run unless --apply. Run from the repo root.
apply=${1:-}
git worktree list --porcelain | awk '/^worktree /{w=$2} /^branch /{sub("refs/heads/","",$2); print w, $2}' |
while read -r wt br; do
  case "$wt" in */.worktrees/*) ;; *) continue ;; esac
  [ -n "$(gh pr list --head "$br" --state merged --json number --jq '.[].number' 2>/dev/null)" ] || continue
  if [ -n "$(git -C "$wt" status --porcelain 2>/dev/null)" ]; then echo "keep (dirty): $wt [$br]"; continue; fi
  if [ "$apply" = --apply ]; then
    git worktree remove --force "$wt" && git branch -D "$br" >/dev/null && echo "removed: $wt [$br]"
  else
    echo "would remove: $wt [$br]"
  fi
done
