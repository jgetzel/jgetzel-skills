#!/usr/bin/env bash
# Orchestrator watcher; run from the repo root with run_in_background.
# Level-triggered, so a restart surfaces anything missed while no watcher ran.
# Exits on: a non-draft PR whose checks finished, or any of whose checks failed
# while others still run, in a state not in handled ("<n> <sha>" handles every
# state at that SHA; "<n> <sha> <state>" only that one, so a later state such as
# the remaining checks finishing re-arms it), a change in the newest main run
# (completed, or a job already failed; confirmed on a second poll),
# a $WATCH_PREFIX agent idle >= 15 polls, or a 30-minute heartbeat.
D=.claude/orchestrator; mkdir -p "$D"; H=$D/handled; ST=$D/idle.state; touch "$H"
P=${WATCH_PREFIX:-w}
# State: pending | DIRTY (conflicts; gets no CI) | NOCHECKS (to main, no checks 5+ min after
# its last update: pushed before a retarget) | FAILING:<failed checks>+pending | <unique conclusions>.
prs() { gh pr list --json number,headRefOid,isDraft,statusCheckRollup,mergeStateStatus,baseRefName,updatedAt --jq '.[]|select(.isDraft|not)|(.statusCheckRollup // []) as $c|([$c[]|select(.status=="COMPLETED" and (.conclusion|IN("FAILURE","CANCELLED","TIMED_OUT","STARTUP_FAILURE","ACTION_REQUIRED")))|.name|gsub(" ";"_")]) as $f|([$c[]|select(.status!="COMPLETED")]|length) as $p|"\(.number) \(.headRefOid[:7]) \(if .mergeStateStatus=="DIRTY" then "DIRTY" elif ($c|length)==0 then (if .baseRefName=="main" and (now-(.updatedAt|fromdate))>300 then "NOCHECKS" else "pending" end) elif $p>0 and ($f|length)>0 then "FAILING:\($f|join(","))+pending" elif $p>0 then "pending" else ([$c[]|.conclusion]|unique|join(",")) end)"' 2>/dev/null; }
actionable() { prs | while read -r n sha st; do [ "$st" = pending ] || grep -qxF -e "$n $sha" -e "$n $sha $st" "$H" || echo "ACTION PR #$n @$sha: $st  (mark: echo \"$n $sha\" or \"$n $sha $st\")"; done; }
# --status completed --limit 1 sometimes returns a stale run; sort instead.
# Newest run only: a rerun requeues an old run, which must not look like a change.
main() {
  local r; r=$(gh run list --branch main --event push --limit 10 --json databaseId,conclusion,headSha,status,createdAt --jq 'sort_by(.createdAt)|last|"\(.databaseId) \(.headSha[:7]) \(.status) \(.conclusion)"' 2>/dev/null) || return
  set -- $r; [ $# -ge 3 ] || return
  if [ "$3" = completed ]; then echo "main $2 $4"; return; fi
  local f; f=$(gh run view "$1" --json jobs --jq '[.jobs[]|select(.conclusion=="failure" or .conclusion=="cancelled" or .conclusion=="timed_out")|.name|gsub(" ";"_")]|join(",")' 2>/dev/null)
  [ -n "$f" ] && echo "main $2 FAILING:$f"
}
idle() { herdr agent list 2>/dev/null | P="$P" python3 -c 'import os,sys,json;[print(a["name"]) for a in json.load(sys.stdin)["result"]["agents"] if a.get("name","").startswith(os.environ["P"]) and a["agent_status"]!="working"]'; }
declare -A n; [ -f "$ST" ] && source "$ST"
m0=$(main)
for i in $(seq 30); do
  a=$(actionable); [ -n "$a" ] && { echo "$a"; exit 0; }
  m=$(main); if [ -n "$m" ] && [ "$m" != "$m0" ]; then sleep 20; [ "$(main)" = "$m" ] && { echo "$m0 -> $m"; exit 0; }; fi
  ids=$(idle); for x in "${!n[@]}"; do grep -qx "$x" <<<"$ids" || unset "n[$x]"; done
  for x in $ids; do n[$x]=$(( ${n[$x]:-0} + 1 )); [ "${n[$x]}" -ge 15 ] && { echo "idle 15m: $x (read its pane)"; unset "n[$x]"; declare -p n > "$ST"; exit 0; }; done
  declare -p n > "$ST"; sleep 60
done
echo heartbeat
