#!/bin/sh
# Made-up spaces, agents and shells for screenshots of the rework rail (rw-rail), then the rework layout. Run inside
# shot.sh's sandbox, never in the person's window:
#   swarm/herdr/shot.sh --before 'sh swarm/herdr/rail-demo.sh [--fold]' out.png
# Agents are shells that print a status report (OSC 7501) and a title, then wait; a helper started from inside one
# gets it as its parent. --fold folds jk_ledger, nixos and linn-studio (shells only). A second hc session on this
# machine stands in for another machine, "desktop"; it stops once shot.sh removes the sandbox.
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
linn=$(do_ space.new --name linn-studio --folder "$(dir linn-studio)" | id space)
jk=$(do_ space.new --name jk_ledger --folder "$(dir jk_ledger)" \
  --argv "$(agent working 'fix login redirect' 'helper|working|run the auth tests' 'explore|working|find callers of rotate()')" | id space)
tab "$jk" "$(agent done 'write the 0071 migration')"
tab "$jk" "$(agent blocked 'run rm -rf dist?' | sed 's/app=claude/app=codex/')"
tab "$jk" "$(agent idle 'review PR 88')"
tab "$jk" '["python3","-m","http.server","8731"]'
tab "$jk" '["zsh"]'
# A swarm: agents title themselves with their name, so the row shows their folder instead.
do_ space.new --name high-perf-lean --folder "$(dir high-perf-lean)" --argv "$(agent done hpl-comms3 \
  'hpl-370|done|hpl-370' 'hpl-371|working|hpl-371')" >/dev/null
# A space with no terminal: its only tab is a mod pane.
docs=$(do_ space.new --name notes --folder "$(dir notes)")
do_ tab.new --space "$(echo "$docs" | jq -r .space)" --mod files >/dev/null
do_ tab.close --id "$(echo "$docs" | jq -r .tab)" --confirmed true >/dev/null

if [ -n "$fold" ]; then
  mkdir -p "$HERDR_APP_HOME/data/rw-rail"
  jq -n --arg f "$(jq -cn --arg a "$jk" --arg b "$nix" --arg c "$linn" '[$a,$b,$c]')" '{folded: $f}' >"$HERDR_APP_HOME/data/rw-rail/store.json"
fi

# "desktop": spaces named like this computer's, with shells.
ds=${HC_SESSION}d
hc machine add --via 'sh -c' --name desktop --session "$ds" >/dev/null
(while [ -d "$HERDR_APP_HOME" ]; do sleep 2; done; HC_SESSION=$ds hc server stop
  rm -rf "${XDG_STATE_HOME:-$HOME/.local/state}/herdr-core/$ds") >/dev/null 2>&1 &
for _ in 1 2 3 4 5 6 7 8 9 10; do # until the window has connected to it
  dn=$(do_ space.new --machine desktop --name nixos --folder /tmp 2>/dev/null | id space) || :
  case $dn in desktop/*) break ;; esac; sleep 1
done
do_ tab.new --space "$dn" --argv '["sh","-c","exec sleep 1d"]' >/dev/null
do_ space.new --machine desktop --name jk_ledger --folder /tmp >/dev/null
sleep 2 # the helpers start and report
do_ layout.switch --name rework >/dev/null
do_ layout.hide --id panel >/dev/null
do_ space.select --id "$jk" >/dev/null
first=$(herdr-app ls | jq -r --arg s "$jk" '[.. | objects | select(.id? == $s)][0] | [.. | objects | select(.pane? != null)][0].pane')
[ "$first" = null ] || do_ pane.focus --pane "$first" >/dev/null
