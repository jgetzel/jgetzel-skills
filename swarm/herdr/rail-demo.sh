#!/bin/sh
# Made-up spaces, agents and shells for screenshots of the rework rail (rw-rail), then the rework layout. Run inside
# shot.sh's sandbox, never in the person's window:
#   swarm/herdr/shot.sh --before 'sh swarm/herdr/rail-demo.sh [--fold]' out.png
# Agents are shells that print a status report (OSC 7501) and a title, then wait; a helper started from inside one
# gets it as its parent. --fold folds jk_ledger and nixos.
set -eu
[ -n "${HERDR_APP_HOME:-}" ] && case $HERDR_APP_HOME in /tmp/hs.*) ;; *) false ;; esac ||
  { echo "rail-demo.sh: only inside shot.sh's sandbox" >&2; exit 2; }
fold=; [ "${1:-}" = --fold ] && fold=1
D=$(dirname "$HERDR_APP_HOME")
do_() { herdr-app do "$@"; }
id() { jq -r ".$1"; }
dir() { mkdir -p "$D/w/$1"; echo "$D/w/$1"; }
# agent <state> <title> [helper lines]: argv for a fake agent; each helper is "<name>|<state>|<title>"
agent() {
  s=$1 title=$2; shift 2
  kids=
  for k in "$@"; do
    n=${k%%|*} r=${k#*|} ks=${r%%|*} kt=${r#*|}
    kids="$kids hc run --bg --name $n -- sh -c 'printf \"\\033]0;$kt\\007\\033]7501;state=$ks:app=claude\\033\\\\\\\\\"; exec sleep 1d' >/dev/null;"
  done
  jq -cn --arg c "printf '\\033]0;$title\\007\\033]7501;state=$s:app=claude\\033\\\\'; $kids exec sleep 1d" '["sh","-c",$c]'
}
tab() { do_ tab.new --space "$1" --argv "$2" >/dev/null; }

nix=$(do_ space.new --name nixos --folder "$(dir nixos)" --argv "$(agent done 'flake update')" | id space)
tab "$nix" '["zsh"]'
do_ space.new --name linn-studio --folder "$(dir linn-studio)" >/dev/null
jk=$(do_ space.new --name jk_ledger --folder "$(dir jk_ledger)" \
  --argv "$(agent working 'fix login redirect' 'helper|working|run the auth tests' 'explore|working|find callers of rotate()')" | id space)
tab "$jk" "$(agent done 'write the 0071 migration')"
tab "$jk" "$(agent blocked 'run rm -rf dist?' | sed 's/app=claude/app=codex/')"
tab "$jk" "$(agent idle 'review PR 88')"
tab "$jk" '["python3","-m","http.server","8731"]'
tab "$jk" '["zsh"]'
do_ space.new --name high-perf-lean --folder "$(dir high-perf-lean)" --argv '["sh","-c","exec sleep 1d"]' >/dev/null
# A space with no terminal: its only tab is a mod pane.
docs=$(do_ space.new --name notes --folder "$(dir notes)")
do_ tab.new --space "$(echo "$docs" | jq -r .space)" --mod files >/dev/null
do_ tab.close --id "$(echo "$docs" | jq -r .tab)" --confirmed true >/dev/null

if [ -n "$fold" ]; then
  mkdir -p "$HERDR_APP_HOME/data/rw-rail"
  jq -n --arg f "$(jq -cn --arg a "$jk" --arg b "$nix" '[$a,$b]')" '{folded: $f}' >"$HERDR_APP_HOME/data/rw-rail/store.json"
fi
sleep 2 # the helpers start and report
do_ layout.switch --name rework >/dev/null
do_ layout.hide --id panel >/dev/null
do_ space.select --id "$jk" >/dev/null
first=$(herdr-app ls | jq -r --arg s "$jk" '[.. | objects | select(.id? == $s)][0] | [.. | objects | select(.pane? != null)][0].pane')
[ "$first" = null ] || do_ pane.focus --pane "$first" >/dev/null
