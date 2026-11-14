#!/bin/sh
# Made-up spaces, agents and shells for screenshots of the rework rail (rw-rail), then the rework layout. Run inside
# shot.sh's sandbox, never in the person's window:
#   swarm/herdr/shot.sh --before 'sh swarm/herdr/rail-demo.sh [--fold] [--swarm 5|24]' out.png
# Agents are shells that print a status report (OSC 7501) and a title, then wait; a helper started from inside one
# gets it as its parent. --fold folds jk_ledger, nixos and linn-studio (shells only). --swarm N adds a space,
# jgetzel-skills, whose repo has a swarm of N agents (5: the rail board's C, 24: its D) that register their own
# terminals in its board, and shows it. A second hc session on this machine stands in for another machine, "desktop";
# it stops once shot.sh removes the sandbox.
set -eu
[ -n "${HERDR_APP_HOME:-}" ] && case $HERDR_APP_HOME in /tmp/hs.*) ;; *) false ;; esac ||
  { echo "rail-demo.sh: only inside shot.sh's sandbox" >&2; exit 2; }
fold= sw=
while [ $# -gt 0 ]; do
  case $1 in --fold) fold=1; shift ;; --swarm) sw=$2; shift 2 ;; *) echo "rail-demo.sh: unknown $1" >&2; exit 2 ;; esac
done
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

folds=; [ -z "$fold" ] || folds="$jk $nix $linn"
if [ -n "$sw" ]; then
  # The swarm: a repo whose board the swarm CLI made, its agents and tasks; each fake agent records its own terminal.
  repo=$(dir jgetzel-skills); git -C "$repo" init -q
  (cd "$repo" && env -u SWARM_DB SWARM_NAME=human "$D/swarm" task add seed && env -u SWARM_DB SWARM_NAME=human "$D/swarm" limits --min 0 --max 99) >/dev/null 2>&1
  db=$repo/.git/swarm/swarm.db now=$(date +%s)
  sqlite3 -cmd ".timeout 9000" "$db" "delete from task; insert or replace into meta(k, v) values('comms', 'll-comms')"
  cat >"$D/w/reg.sh" <<'EOF'
sqlite3 -cmd ".timeout 9000" "$1" "insert or replace into agent(name, hc, status, last_active, started, stay) values('$2', '$HC_TERMINAL_ID', '$3', $4, 1, nullif('$5', ''))"
EOF
  # swagent <name> <db status> <seconds idle> <stay> <agent args...>: a fake agent that registers, then as agent()
  swagent() {
    n=$1 st=$2 ago=$3 stay=$4; shift 4
    jq -cn --arg c "sh '$D/w/reg.sh' '$db' '$n' '$st' $((now - ago)) '$stay'; $(agent "$@" | jq -r '.[2]')" '["sh","-c",$c]'
  }
  task() { sqlite3 -cmd ".timeout 9000" "$db" "insert into task(id, title, state, owner, question) values($1, '$2', '$3', nullif('${4:-}', ''), nullif('${5:-}', ''))"; }
  skills=$(do_ space.new --name jgetzel-skills --folder "$repo" --argv "$(swagent ll-comms idle 120 '' done ll-comms)" | id space)
  if [ "$sw" = 5 ]; then
    tab "$skills" "$(swagent ll-97 working 0 '' idle ll-97)"; task 133 'Lean proofs: crash safety between any two steps' blocked ll-97 'Spawn.unreserve ends the row but keeps its locks. Fix it in this PR, or as its own task?'
    tab "$skills" "$(swagent ll-110 working 0 '' working ll-110 'research|working|read the mod guide')"; task 146 'Rail swarm block' claimed ll-110
    tab "$skills" "$(swagent ll-111 working 0 '' working ll-111)"; task 145 'Bar pills' claimed ll-111
    tab "$skills" "$(swagent ll-107 idle 3660 '' done ll-107)"; task 142 'Pane cards' claimed ll-107
    task 150 'Collapsed rail' open; task 151 'Settings' open
    folds="$nix $linn"
  else
    tab "$skills" "$(swagent ll-203 working 0 '' idle ll-203)"; task 214 'Swarm tab' blocked ll-203 'Keep the old panel?'
    tab "$skills" "$(swagent ll-205 working 0 '' idle ll-205)"; task 231 'Machines' blocked ll-205 'Which machine is the vps?'
    tab "$skills" "$(swagent ll-209 idle 3480 reviews idle ll-209)"; task 222 'Review queue' claimed ll-209
    sqlite3 -cmd ".timeout 9000" "$db" "insert into event(ts, agent, kind, data) values($((now - 60)), 'll-209', 'stay-hung', '')"
    i=210; while [ $i -le 223 ]; do # 14 working, ll-211 among them (you opened it)
      tab "$skills" "$(swagent ll-$i working 0 '' working ll-$i)"; task $((i + 1000)) "Task $i" claimed ll-$i; i=$((i + 1))
    done
    for i in 224 225 226 227 228 229; do tab "$skills" "$(swagent ll-$i idle 1800 '' done ll-$i)"; done
    sqlite3 -cmd ".timeout 9000" "$db" "with recursive n(i) as (select 1 union all select i + 1 from n where i < 31) insert into task(id, title, state) select 2000 + i, 'Later '||i, 'open' from n"
    folds="$jk $nix $linn"
  fi
  tab "$skills" "$(agent working 'read the watchd log')"
  tab "$skills" '["zsh"]'
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
n=0; while [ -n "$sw" ] && [ $n -lt 30 ] && [ "$(sqlite3 -cmd ".timeout 9000" "$db" "select count(*) from agent")" -lt "$sw" ]; do
  sleep 1; n=$((n + 1)) # every swarm agent has recorded its terminal
done
# The swarm tab's sections: context sizes, messages and main's CI; ll-97's question card: lease, files, a compaction.
[ "$sw" != 5 ] || sqlite3 -cmd ".timeout 9000" "$db" "update agent set ctx_tokens = case name when 'll-97' then 221000 when 'll-110' then 51000
  when 'll-111' then 61000 when 'll-107' then 121000 else 82000 end;
  insert into msg(ts, frm, dest, body, kind) values($((now - 6780)), 'll-97', 'll-comms', 'Walker and step solver now close every CLI group but State and Watchd.', 'dm'),
  ($((now - 3240)), 'swarm', 'll-97', 'Context is about 330k tokens: commit, note the task, then compact.', 'system'),
  ($((now - 120)), 'll-comms', 'll-107', 'The verdict is already clear. Stop after the round now running, write up, and close #142.', 'dm');
  insert into ci(id, sha, status, conclusion, url, created, workflow) values(1, '08cc4a8', 'completed', 'success', '', '$(date -u +%Y-%m-%dT%H:%M:%SZ)', 'swarm-lean');
  update task set lease_until = $((now + 5280)), first_claimed_at = $((now - 15360)) where id = 133;
  update agent set status = 'idle', last_active = $((now - 360)), snap = '{\"files\":[\"swarm/lean/SwarmLean/Proofs/Crash.lean\",
    \"swarm/lean/SwarmLean/Proofs/Watchd.lean\",\"swarm/lean/SwarmLean/Db/Spawn.lean\",\"swarm/lean/SwarmLean/Lib/Spawn.lean\",
    \"swarm/lean/SwarmLean/Lib/Conflict.lean\",\"swarm/lean/SwarmLean/Cmd/State.lean\"]}' where name = 'll-97';
  insert into event(ts, agent, kind, data) values($((now - 9000)), 'll-97', 'compact', '')"
opened=[]; [ "$sw" != 24 ] || opened=$(sqlite3 -cmd ".timeout 9000" "$db" "select json_array(hc) from agent where name='ll-211'")
# With a swarm, this computer's other spaces fold (shot.sh's demo and notes too), as on the rail board.
[ -z "$sw" ] || folds="$folds $(herdr-app ls | jq -r '.. | objects | select(.name? == "demo" or .name? == "notes" or .name? == "high-perf-lean") | .id? // empty' | grep -v / || :)"
if [ -n "$folds$sw" ]; then
  mkdir -p "$HERDR_APP_HOME/data/rw-rail"
  jq -n --arg f "$(printf '%s\n' $folds | jq -Rcs 'split("\n") | map(select(. != ""))')" --arg o "$opened" '{folded: $f, opened: $o}' \
    >"$HERDR_APP_HOME/data/rw-rail/store.json"
fi
do_ layout.switch --name rework >/dev/null
do_ layout.hide --id panel >/dev/null
show=$jk; [ -z "$sw" ] || show=$skills
do_ space.select --id "$show" >/dev/null
first=$(herdr-app ls | jq -r --arg s "$show" '[.. | objects | select(.id? == $s)][0] | [.. | objects | select(.pane? != null)][0].pane')
[ "$first" = null ] || do_ pane.focus --pane "$first" >/dev/null
