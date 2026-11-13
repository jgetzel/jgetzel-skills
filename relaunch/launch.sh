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

# Prints "<space id> <tab id>" of the window tab showing terminal $1, or nothing (also when no window runs here).
where() { herdr-app ls 2>/dev/null | jq -r --arg a "$1" 'first(.spaces[]? as $s | $s.tabs[] as $t | $t.terminals[]
  | select(.terminal == $a) | "\($s.id) \($t.id)") // ""' 2>/dev/null || true; }
# The window labels every terminal it shows with its space and tab, and hc keeps the labels, so this works
# when the window runs on another machine; ask the local window only when the labels are missing.
space=${SWARM_SPACE:-} tab=
[ -n "$space" ] || read -r space tab <<<"$(hc get "$HC_TERMINAL_ID" 2>/dev/null |
  jq -r '(.labels | objects) // {} | "\(.["herdr.space"] // "") \(.["herdr.tab"] // "")"' 2>/dev/null || true)"
[ -n "$space" ] || read -r space tab <<<"$(where "$HC_TERMINAL_ID")"
[ -n "$space" ] || { echo "launch.sh: $HC_TERMINAL_ID has no herdr.space label and no Herdr window here shows it" >&2; exit 1; }
labels=(--label "herdr.space=$space")
[ "$place" = split ] && labels+=(--label "herdr.tab=$tab")

# hc passes your environment on. Claude Code's variables would make the agent a
# child session (no transcript, missing from ListAgents); herdr's would point
# it at the old multiplexer.
unset_vars=()
for v in $(compgen -e); do case $v in CLAUDE* | HERDR*) unset_vars+=(-u "$v") ;; esac; done

# Where a systemd user session exists, claude runs in its own scope: a cgroup per agent (exact memory.peak and
# cpu.stat for the swarm, cgroup.kill when it ends). The unit name carries a nonce: a successor shares the name.
scope=()
if command -v systemd-run >/dev/null && [ -S "${XDG_RUNTIME_DIR:-/nonexistent}/systemd/private" ]; then
  scope=(systemd-run --user --scope --quiet --collect "--unit=swarm-agent-$name-$$" --)
fi

out=$(hc run --json --bg --outlive-parent --no-notify --name "$name" --cwd "$PWD" "${labels[@]}" \
  -- env "${unset_vars[@]+"${unset_vars[@]}"}" ${scope[@]+"${scope[@]}"} claude -n "$name" "$@" "$task")
addr=$(jq -r .address <<<"$out")

# The agent runs now: report it, and treat naming the tab as best effort.
echo "$addr"
set +e
# The window numbers a new tab; name it once the window has placed the terminal.
if [ "$place" = tab ] && herdr-app status >/dev/null 2>&1; then # a window on another machine names its own tabs
  for _ in $(seq 20); do
    read -r _ id <<<"$(where "$addr")"
    [ -n "$id" ] && { herdr-app do tab.rename --id "$id" --name "$name" >/dev/null; break; }
    sleep 0.5
  done
  [ -n "${id:-}" ] || echo "launch.sh: $addr has no tab yet; left unnamed" >&2
fi
exit 0
