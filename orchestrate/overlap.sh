#!/usr/bin/env bash
# Pre-merge check for a PR: textual conflicts with origin/main, the merges that
# landed since the PR's base, and the files both sides changed (read those
# hunks for semantic conflicts: changed signatures, new strict fields).
# Usage: overlap.sh <pr-number>   (run from the repo root)
set -euo pipefail
pr=$1
git fetch -q origin
branch=$(gh pr view "$pr" --json headRefName --jq .headRefName)
head="origin/${branch}"
base=$(git merge-base origin/main "$head")

echo "== #$pr ($branch) vs origin/main"
if conflicts=$(git merge-tree --write-tree --name-only origin/main "$head" | tail -n +2) && [ -z "$conflicts" ]; then
  echo "textual: clean"
else
  echo "textual: CONFLICTS"; echo "$conflicts"
fi

echo "== merged since its base"
git log --oneline "${base}..origin/main"

echo "== files both sides changed"
comm -12 <(git diff --name-only "$base" origin/main | sort) <(git diff --name-only "$base" "$head" | sort)

echo "== CI start vs base"
gh pr view "$pr" --json statusCheckRollup --jq '.statusCheckRollup[] | select(.startedAt != null) | "\(.name) \(.startedAt) \(.conclusion)"'
