#!/usr/bin/env bash
# Start Claude Code agent <name> in the Herdr window from inside a Herdr terminal:
# in a new tab named <name> (tab), or as a split of your own tab (split).
# It outlives you and types no notes into you; its first message is <task>.
# Prints its hc address. Run from the folder the agent should start in.
#   launch.sh <name> tab|split <task> [claude args...]
set -euo pipefail
[ $# -ge 3 ] || { echo "usage: launch.sh <name> tab|split <task> [claude args...]" >&2; exit 2; }
[ -n "${HC_TERMINAL_ID:-}" ] || { echo "launch.sh: not in a Herdr terminal (no HC_TERMINAL_ID)" >&2; exit 2; }
name=$1 place=$2 task=$3; shift 3
case $place in tab | split) ;; *) echo "launch.sh: place is tab or split, not $place" >&2; exit 2 ;; esac

# Prints "<space id> <tab id>" of the window tab showing terminal $1, or nothing.
where() { herdr-app ls | ADDR="$1" python3 -c 'import json,os,sys
print(next((s["id"]+" "+t["id"] for s in json.load(sys.stdin)["spaces"] for t in s["tabs"] if any(x["terminal"]==os.environ["ADDR"] for x in t["terminals"])),""))'; }
read -r space tab <<<"$(where "$HC_TERMINAL_ID")"
[ -n "$space" ] || { echo "launch.sh: $HC_TERMINAL_ID is not shown in the Herdr window" >&2; exit 1; }
labels=(--label "herdr.space=$space")
[ "$place" = split ] && labels+=(--label "herdr.tab=$tab")

# hc passes your environment on. Claude Code's variables would make the agent a
# child session (no transcript, missing from ListAgents); herdr's would point
# it at the old multiplexer.
unset_vars=()
for v in $(compgen -e); do case $v in CLAUDE* | HERDR*) unset_vars+=(-u "$v") ;; esac; done

out=$(hc run --json --bg --outlive-parent --no-notify --name "$name" --cwd "$PWD" "${labels[@]}" \
  -- env "${unset_vars[@]}" claude -n "$name" "$@" "$task")
addr=$(python3 -c 'import json,sys;print(json.loads(sys.argv[1])["address"])' "$out")

# The agent runs now: report it, and treat naming the tab as best effort.
echo "$addr"
set +e
# The window numbers a new tab; name it once the window has placed the terminal.
if [ "$place" = tab ]; then
  for _ in $(seq 20); do
    read -r _ id <<<"$(where "$addr")"
    [ -n "$id" ] && { herdr-app do tab.rename --id "$id" --name "$name" >/dev/null; break; }
    sleep 0.5
  done
  [ -n "${id:-}" ] || echo "launch.sh: $addr has no tab yet; left unnamed" >&2
fi
exit 0
