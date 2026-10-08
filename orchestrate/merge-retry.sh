#!/usr/bin/env bash
# Usage: merge-retry.sh PR... — every 3 min for up to 2 h, squash-merge each PR
# whose current head has all checks completed (success/skipped) and is MERGEABLE.
# Exits when all are merged, or reports what's left.
left=("$@")
for i in $(seq 40); do
  next=()
  for n in "${left[@]}"; do
    info=$(gh pr view "$n" --json state,mergeable,headRefOid,statusCheckRollup --jq '"\(.state) \(.mergeable) \(.headRefOid[:7]) \(if (.statusCheckRollup|length)>0 and ([.statusCheckRollup[]|select(.status!="COMPLETED" or (.conclusion!="SUCCESS" and .conclusion!="SKIPPED"))]|length)==0 then "green" else "notgreen" end)"' 2>/dev/null)
    read -r state mergeable sha checks <<<"$info"
    if [ "$state" = MERGED ]; then echo "$(date +%H:%M) #$n merged"; continue; fi
    if [ "$checks" = green ] && [ "$mergeable" = MERGEABLE ]; then
      gh pr merge "$n" --squash --match-head-commit "$(gh pr view "$n" --json headRefOid --jq .headRefOid)" >/dev/null 2>&1
      [ "$(gh pr view "$n" --json state --jq .state 2>/dev/null)" = MERGED ] && { echo "$(date +%H:%M) #$n merged @$sha"; continue; }
    fi
    echo "$(date +%H:%M) #$n waiting: ${info:-api-error}"
    next+=("$n")
  done
  left=("${next[@]}"); [ ${#left[@]} -eq 0 ] && { echo ALL MERGED; exit 0; }
  sleep 180
done
echo "gave up after 2h: ${left[*]}"; exit 1
