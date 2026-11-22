#!/bin/sh
# A swarm agent's prompt, as Claude Code's PermissionRequest hook sees it (UI-SPEC II.6d), for Needs you to show.
# record: the hook's JSON on stdin (tool_name, tool_input) to <db dir>/prompts/<agent>.json; clear: removes it (on
# PostToolUse and Stop). Display only: it prints nothing and always exits 0, so the prompt shows as it would anyway.
umask 077 # the record and its dir: the user's only (L3); peers are the same user, so the cards check it (H3)
[ -n "$SWARM_NAME" ] || { [ "$1" != record ] || cat >/dev/null; exit 0; }
db=${SWARM_DB:-${XDG_STATE_HOME:-$HOME/.local/state}/swarm/swarm.db}
d=${db%/*}/prompts
f=$d/$SWARM_NAME.json
case $1 in
  record) mkdir -p "$d"; head -c 262144 >"$f.tmp" && mv -f "$f.tmp" "$f"; cat >/dev/null ;; # a long Write: kept cut, read whole
  clear) [ ! -e "$f" ] || rm -f "$f" ;;
esac
exit 0
