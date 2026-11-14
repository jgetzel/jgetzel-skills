#!/bin/sh
# Made-up spaces, agents and shells for screenshots of the rework (rw-* mods), then the rework layout. Run inside
# shot.sh's sandbox, never in the person's window; shot.sh --rework <preset> runs it:
#   swarm/herdr/shot.sh --rework real|large|small out.png
#   swarm/herdr/shot.sh --before 'sh swarm/herdr/rail-demo.sh [--preset P] [--fold] [--swarm 5|24 [--two]] [--vps]' out.png
# Presets (no flags: real):
# - real: about the user's window. Ten spaces on this computer, 15 agents. Two swarms shaped as `swarm spawn` makes them:
#   jgetzel-skills' communicator ll-comms joined in its space (the db's space, its terminal's swarm.comms label), a
#   watchd terminal with no pane that the registry (`swarm state --view swarms`) lists, workers started with
#   --outlive-parent from the communicator's terminal, from watchd's (auto-spawn) or from an earlier communicator's
#   that has ended; one asks, one is hung, one has a helper, four ended. high-perf-lean runs hpl, one of them asking.
#   As in the user's window (#175), the spaces' folders are off: jgetzel-skills' is the home folder, high-perf-lean's
#   the jgetzel-skills repo. Plain spaces hold agents, a sub-agent, codex and shells. "desktop" has spaces of the same
#   names; "vps" is unreachable.
# - large: real, with jgetzel-skills at 24 live agents and 110 ended.
# - small: the rail's first demo; with no other flag no swarm, else as the flags say.
# Agents are shells that print a status report (OSC 7501) and a title, then wait; a helper started from inside one gets
# it as its parent. Flags imply small. --fold folds jk_ledger, nixos and linn-studio (shells only). --swarm N adds a
# space, jgetzel-skills, whose repo has a swarm of N agents (5: the rail board's C, 24: its D) that register their own
# terminals in its board, started from the communicator's terminal, and shows it. A second hc session on this machine
# stands in for another machine, "desktop"; it stops once shot.sh removes the sandbox. --vps adds a third, "vps", with a
# space whose agent asks; it is unreachable while $HERDR_APP_HOME/vps.down exists and its hc is stopped
# (HC_SESSION=${HC_SESSION}v hc server stop). --two makes high-perf-lean a second swarm, hpl, with 5 agents, one of them
# asking (the All swarms view).
set -eu
[ -n "${HERDR_APP_HOME:-}" ] && case $HERDR_APP_HOME in /tmp/hs.*) ;; *) false ;; esac ||
  { echo "rail-demo.sh: only inside shot.sh's sandbox" >&2; exit 2; }
preset=real fold= sw= vps= two=
while [ $# -gt 0 ]; do
  case $1 in
    --preset) preset=$2; shift 2 ;;
    --fold) fold=1 preset=small; shift ;;
    --swarm) sw=$2 preset=small; shift 2 ;;
    --vps) vps=1 preset=small; shift ;;
    --two) two=1 preset=small; shift ;;
    *) echo "rail-demo.sh: unknown $1" >&2; exit 2 ;;
  esac
done
case $preset in small|real|large) ;; *) echo "rail-demo.sh: no preset $preset (small, real, large)" >&2; exit 2 ;; esac
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

# A swarm: a repo whose board the swarm CLI made, its agents and tasks; each fake agent records its own terminal. The
# helpers below write to $db as they run.
now=$(date +%s)
sql() { sqlite3 -cmd ".timeout 9000" "$db" "$@"; }
# board <repo> <comms> <min> <max>: a git repo whose board the swarm CLI made, no tasks, <comms> its communicator; sets db
board() {
  git -C "$1" init -q
  (cd "$1" && env -u SWARM_DB SWARM_NAME=human "$D/swarm" task add seed && env -u SWARM_DB SWARM_NAME=human "$D/swarm" limits --min "$3" --max "$4") >/dev/null 2>&1
  db=$1/.git/swarm/swarm.db
  sql "delete from task; insert or replace into meta(k, v) values('comms', '$2')"
}
cat >"$(dir .)/reg.sh" <<'EOF'
sqlite3 -cmd ".timeout 9000" "$1" "insert or replace into agent(name, hc, status, last_active, started, stay, claude_pid) values('$2', '$HC_TERMINAL_ID', '$3', $4, 1, nullif('$5', ''), $PPID)"
EOF
# swagent <name> <db status> <seconds idle> <stay> <agent args...>: a fake agent that registers, then as agent()
swagent() {
  n=$1 st=$2 ago=$3 stay=$4; shift 4
  jq -cn --arg c "sh '$D/w/reg.sh' '$db' '$n' '$st' $((now - ago)) '$stay'; $(agent "$@" | jq -r '.[2]')" '["sh","-c",$c]'
}
task() { sql "insert into task(id, title, state, owner, question) values($1, '$2', '$3', nullif('${4:-}', ''), nullif('${5:-}', ''))"; }
# wtab <space> <communicator's terminal> <argv>: a worker started from the communicator's terminal (so that is its
# parent), opting into the space; Herdr gives it a tab there.
wtab() { hc run --bg --json --parent "$2" --label "herdr.space=$1" -- sh -c "$(echo "$3" | jq -r '.[2]')" >/dev/null; }
# spawn <parent terminal> <space> <swagent args...>: a worker as `swarm spawn` starts one (launch.sh): named, in its
# worktree, outliving its parent, opting into the swarm's space
spawn() {
  p=$1 s=$2 wt=$(dir "$(basename "${db%/.git/swarm/swarm.db}")-$3"); shift 2
  hc run --bg --json --parent "$p" --outlive-parent --no-notify --name "$1" --cwd "$wt" --label "herdr.space=$s" -- sh -c "$(swagent "$@" | jq -r '.[2]')" >/dev/null
}
# join <space> <terminal>: what `swarm join` records for a communicator: the db's space, the terminal's swarm.comms label
join() { sql "insert or replace into meta(k, v) values('space', '$1')"; hc label "$2" "swarm.comms=$db" >/dev/null; }
# watchd <repo> <comms>: a watchd as `swarm watchd --restart` starts one, a terminal with no parent and so no pane, in
# the db and in the registry of swarms on this machine; sets wd (its terminal)
watchd() {
  wd=$(hc run --bg --json --no-parent --no-notify --cwd "$1" -- sh -c "echo \$\$ >'$1/.git/watchd.pid'; exec sleep 1d" | id address)
  until [ -s "$1/.git/watchd.pid" ]; do sleep 0.2; done
  pid=$(cat "$1/.git/watchd.pid") reg=${XDG_STATE_HOME:?shot.sh sets it}/swarm/swarms
  sql "insert or replace into meta(k, v) values('watchd', '$pid $wd')"
  mkdir -p "$reg"
  jq -cn --arg db "$db" --arg f "$1" --arg c "$2" --argjson p "$pid" --argjson s "$now" \
    '{db: $db, folder: $f, tag: ($c | sub("-comms$"; "")), comms: $c, pid: $p, started: $s}' >"$reg/$(echo "$db" | tr / %).json"
}
# await <n>: until n of $db's agents are live, each having recorded its terminal
await() {
  n=0; while [ $n -lt 30 ] && [ "$(sql "select count(*) from agent where ended is null")" -lt "$1" ]; do sleep 1; n=$((n + 1)); done
}

show=
if [ "$preset" != small ]; then
  # jgetzel-skills: ll-comms in a space whose folder is the home folder (#175); some workers spawned by ll-comms, some
  # by watchd, one by an earlier ll-comms whose terminal has ended. Agents title themselves with their name.
  repo=$(dir jgetzel-skills); board "$repo" ll-comms 0 6; lldb=$db
  made=$(do_ space.new --name jgetzel-skills --folder "$(dir jgetzel)" --argv "$(swagent ll-comms idle 120 '' done ll-comms)")
  show=$(echo "$made" | id space) llc=$(echo "$made" | id terminal)
  join "$show" "$llc"; watchd "$repo" ll-comms
  spawn "$llc" "$show" ll-124 working 0 '' working ll-124 'explore-124|working|find the live shots in GAPS.md'
  task 179 'Herdr rework: make the screenshot sandbox match a real setup (real-shaped swarms, second machine, size presets)' claimed ll-124
  spawn "$wd" "$show" ll-125 working 0 '' idle ll-125
  task 180 'Herdr rework: hardening against hostile input and arbitrary scale (sessions, tabs, swarms)' blocked ll-125 \
    'A rail of 300 terminals takes 2 s to draw. Cap it at 200 rows with a "more" line, or page it?'
  old=$(hc run --bg --json --no-parent --no-notify -- sh -c 'sleep 2' | id address)
  spawn "$old" "$show" ll-126 idle 3480 reviews idle ll-126
  task 171 'watchd: after a compaction, a staying agent or the communicator gets no continue prompt' claimed ll-126
  sql "insert into event(ts, agent, kind, data) values($((now - 60)), 'll-126', 'stay-hung', '')"
  spawn "$llc" "$show" ll-127 idle 1500 '' done ll-127
  task 170 'Crash safety: fix the four stop-between-steps leaks #133 found (F1, F2, F3, F5)' claimed ll-127
  live=5
  if [ "$preset" = large ]; then # 19 more, auto-spawned by watchd
    i=130; while [ $i -le 148 ]; do
      st=working; [ $((i % 4)) != 0 ] || st=idle
      spawn "$wd" "$show" ll-$i $st 0 '' $st ll-$i; task $((i + 1000)) "Task $i" claimed ll-$i; i=$((i + 1))
    done
    sql "with recursive n(i) as (select 1 union all select i + 1 from n where i < 31) insert into task(id, title, state, priority)
      select 2000 + i, 'Later '||i, 'open', i % 3 + 1 from n"
    live=24
  fi
  sql "with recursive n(i) as (select 1 union all select i + 1 from n where i < $((live == 24 ? 110 : 4)))
    insert into agent(name, hc, status, last_active, started, ended, model, wt) select 'll-'||(124 - i), 'tx'||i, 'idle',
    $now - i * 900, $now - i * 900 - 5400, $now - i * 900, 'opus', '/w/jgetzel-skills-ll-'||(124 - i) from n;
    insert into task(id, title, state, owner) values(173, 'Herdr rework: visual gap audit of the build against the canvas', 'done', 'll-120'),
    (174, 'Herdr rework look A: the canvas''s warm palette as the rework layout''s theme', 'done', 'll-121'),
    (175, 'Herdr rework: the live rail draws no swarm block', 'done', 'll-122'), (177, 'Herdr rework look D', 'done', 'll-123'),
    (167, 'Phone app (.apk) to view and message remote agents over hc connect', 'open', null),
    (181, 'swarm board: group done tasks by day', 'open', null);
    insert into msg(ts, frm, dest, body, kind) values($((now - 2400)), 'll-127', 'll-comms', 'PR #342 is ready.', 'dm'),
    ($((now - 300)), 'll-comms', 'll-124', 'Use the real preset for the before/after check.', 'dm');
    insert into ci(id, sha, status, conclusion, url, created, workflow) values(1, 'bea333c', 'completed', 'success', '', '$(date -u +%Y-%m-%dT%H:%M:%SZ)', 'swarm-lean')"
  tab "$show" '["zsh"]'
  await "$live" # reg.sh replaces a row: models and context sizes once all have
  sql "update agent set model = case cast(substr(name, 4) as int) % 3 when 0 then 'opus' when 1 then 'sonnet' else 'fable' end,
    ctx_tokens = 40000 + cast(substr(name, 4) as int) % 9 * 31000 where ended is null and name != 'll-comms'"
  # high-perf-lean: hpl, in a space whose folder is the jgetzel-skills repo (#175)
  board "$(dir high-perf-lean)" hpl-comms 3 3
  made=$(do_ space.new --name high-perf-lean --folder "$repo" --argv "$(swagent hpl-comms idle 300 '' idle hpl-comms)")
  hpl=$(echo "$made" | id space) hplc=$(echo "$made" | id terminal)
  join "$hpl" "$hplc"; watchd "$D/w/high-perf-lean" hpl-comms
  spawn "$hplc" "$hpl" hpl-3 working 0 '' working hpl-3; task 41 'Arena allocator for Expr' claimed hpl-3
  spawn "$wd" "$hpl" hpl-4 idle 1140 '' idle hpl-4; task 44 'Bench: Mathlib import time' blocked hpl-4 \
    'The Mathlib import bench needs 40 G for 25 minutes. Run it now, or wait until the ll swarm is quieter?'
  task 49 'Inline small closures in the compiler pass' open
  sql "insert into ci(id, sha, status, conclusion, url, created, workflow) values(1, 'a1b2c3d', 'in_progress', null, '', '$(date -u +%Y-%m-%dT%H:%M:%SZ)', 'ci')"
  await 3; db=$lldb
  sqlite3 -cmd ".timeout 9000" "$DEMO_DB" "delete from agent" # shot.sh's demo space holds a copy of a real board: not a third swarm
  vps=1
fi

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
[ -n "$two" ] || [ "$preset" != small ] || do_ space.new --name high-perf-lean --folder "$(dir high-perf-lean)" --argv "$(agent done hpl-comms3 \
  'hpl-370|done|hpl-370' 'hpl-371|working|hpl-371')" >/dev/null
# A space with no terminal: its only tab is a mod pane.
docs=$(do_ space.new --name notes --folder "$(dir notes)")
do_ tab.new --space "$(echo "$docs" | jq -r .space)" --mod files >/dev/null
do_ tab.close --id "$(echo "$docs" | jq -r .tab)" --confirmed true >/dev/null
if [ "$preset" != small ]; then
  lua=$(do_ space.new --name lua-lean --folder "$(dir lua-lean)" --argv "$(agent idle 'port the FFI tests')" | id space)
  tab "$lua" '["zsh"]'
  do_ space.new --name dotfiles --folder "$(dir dotfiles)" >/dev/null
  do_ space.new --name housing_search --folder "$(dir housing_search)" --argv "$(agent working 'compare the three listings')" >/dev/null
fi

folds=; [ -z "$fold" ] || folds="$jk $nix $linn"
if [ -n "$sw" ]; then
  repo=$(dir jgetzel-skills); board "$repo" ll-comms 0 99
  made=$(do_ space.new --name jgetzel-skills --folder "$repo" --argv "$(swagent ll-comms idle 120 '' done ll-comms)")
  skills=$(echo "$made" | id space) llc=$(echo "$made" | id terminal) show=$skills
  if [ "$sw" = 5 ]; then
    wtab "$skills" "$llc" "$(swagent ll-97 working 0 '' idle ll-97)"; task 133 'Lean proofs: crash safety between any two steps' blocked ll-97 'Spawn.unreserve ends the row but keeps its locks. Fix it in this PR, or as its own task?'
    wtab "$skills" "$llc" "$(swagent ll-110 working 0 '' working ll-110 'research|working|read the mod guide')"; task 146 'Rail swarm block' claimed ll-110
    wtab "$skills" "$llc" "$(swagent ll-111 working 0 '' working ll-111)"; task 145 'Bar pills' claimed ll-111
    wtab "$skills" "$llc" "$(swagent ll-107 idle 3660 '' done ll-107)"; task 142 'Pane cards' claimed ll-107
    task 150 'Collapsed rail' open; task 151 'Settings' open
    folds="$nix $linn"
  else
    wtab "$skills" "$llc" "$(swagent ll-203 working 0 '' idle ll-203)"; task 214 'Swarm tab' blocked ll-203 'Keep the old panel?'
    wtab "$skills" "$llc" "$(swagent ll-205 working 0 '' idle ll-205)"; task 231 'Machines' blocked ll-205 'Which machine is the vps?'
    wtab "$skills" "$llc" "$(swagent ll-209 idle 3480 reviews idle ll-209)"; task 222 'Review queue' claimed ll-209
    sqlite3 -cmd ".timeout 9000" "$db" "insert into event(ts, agent, kind, data) values($((now - 60)), 'll-209', 'stay-hung', '')"
    i=210; while [ $i -le 223 ]; do # 14 working, ll-211 among them (you opened it)
      wtab "$skills" "$llc" "$(swagent ll-$i working 0 '' working ll-$i)"; task $((i + 1000)) "Task $i" claimed ll-$i; i=$((i + 1))
    done
    for i in 224 225 226 227 228 229; do wtab "$skills" "$llc" "$(swagent ll-$i idle 1800 '' done ll-$i)"; done
    sqlite3 -cmd ".timeout 9000" "$db" "with recursive n(i) as (select 1 union all select i + 1 from n where i < 31) insert into task(id, title, state) select 2000 + i, 'Later '||i, 'open' from n"
    folds="$jk $nix $linn"
  fi
  tab "$skills" "$(agent working 'read the watchd log')"
  tab "$skills" '["zsh"]'
  if [ -n "$two" ]; then # hpl: swagent and task write to $db as they run
    lldb=$db hrepo=$(dir high-perf-lean); board "$hrepo" hpl-comms 8 8
    made=$(do_ space.new --name high-perf-lean --folder "$hrepo" --argv "$(swagent hpl-comms idle 300 '' idle hpl-comms)")
    hpl=$(echo "$made" | id space) hplc=$(echo "$made" | id terminal)
    wtab "$hpl" "$hplc" "$(swagent hpl-4 idle 1140 '' idle hpl-4)"; task 44 'Bench: Mathlib import time' blocked hpl-4 'The Mathlib import bench needs 40 G for 25 minutes. Run it now, or wait until the ll swarm is quieter?'
    wtab "$hpl" "$hplc" "$(swagent hpl-3 working 0 '' working hpl-3)"; task 41 'Arena allocator for Expr' claimed hpl-3
    wtab "$hpl" "$hplc" "$(swagent hpl-6 working 0 '' working hpl-6)"; task 45 'Simp cache keyed by pointer hash' claimed hpl-6
    wtab "$hpl" "$hplc" "$(swagent hpl-7 idle 540 '' idle hpl-7)"; task 47 'CI: perf regression gate' claimed hpl-7
    task 49 'Inline small closures in the compiler pass' open; task 50 'Bench: instantiateMVars on deep terms' open
    sqlite3 -cmd ".timeout 9000" "$db" "insert into ci(id, sha, status, conclusion, url, created, workflow) values(1, 'a1b2c3d', 'in_progress', null, '', '$(date -u +%Y-%m-%dT%H:%M:%SZ)', 'ci')"
    db=$lldb
    sqlite3 -cmd ".timeout 9000" "$DEMO_DB" "delete from agent" # shot.sh's demo space holds a copy of a real board: not a third swarm
  fi
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
if [ -n "$vps" ]; then
  printf '%s\n' '#!/bin/sh' '[ -e "$HERDR_APP_HOME/vps.down" ] && exit 255' 'for a; do last=$a; done' 'exec sh -c "$last"' >"$D/w/via.sh"
  chmod +x "$D/w/via.sh"
  hc machine add --via "$D/w/via.sh" --name vps --session "${HC_SESSION}v" >/dev/null
  (while [ -d "$HERDR_APP_HOME" ]; do sleep 2; done; HC_SESSION=${HC_SESSION}v hc server stop
    rm -rf "${XDG_STATE_HOME:-$HOME/.local/state}/herdr-core/${HC_SESSION}v") >/dev/null 2>&1 &
  for _ in 1 2 3 4 5 6 7 8 9 10; do
    vn=$(do_ space.new --machine vps --name ledger --folder /tmp --argv "$(agent blocked 'deploy to prod?')" 2>/dev/null | id space) || :
    case $vn in vps/*) break ;; esac; sleep 1
  done
  [ "$preset" = small ] || { touch "$HERDR_APP_HOME/vps.down"; HC_SESSION=${HC_SESSION}v hc server stop >/dev/null 2>&1 || :; }
fi
sleep 2 # the helpers start and report
[ -z "$sw" ] || await "$sw"
# launch.sh names a worker's tab after it
[ "$preset" = small ] || herdr-app ls | jq -r '.spaces[].tabs[] | select((.name | test("^[0-9]+$")) and .terminals[0].name != null)
  | "\(.id) \(.terminals[0].name)"' | while read -r t n; do do_ tab.rename --id "$t" --name "$n" >/dev/null; done
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
# The large swarm's table and board: models, 12 ended agents, the next tasks' priorities.
[ "$sw" != 24 ] || sqlite3 -cmd ".timeout 9000" "$db" "update agent set model = case cast(substr(name, 4) as int) % 3 when 0 then 'opus'
  when 1 then 'sonnet' else 'fable' end, ctx_tokens = 40000 + cast(substr(name, 4) as int) % 9 * 31000 where name != 'll-comms';
  with recursive n(i) as (select 1 union all select i + 1 from n where i < 12) insert into agent(name, hc, status, last_active, started,
  ended, model, wt) select 'll-'||(180 + i), 'tx'||i, 'idle', $now - i * 1500, $now - i * 1500 - 5400, $now - i * 1500, 'opus',
  '/w/jgetzel-skills-ll-'||(180 + i) from n;
  update task set priority = (id % 3) + 1 where id > 2000"
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
[ -n "$show" ] || show=$jk
do_ space.select --id "$show" >/dev/null
first=$(herdr-app ls | jq -r --arg s "$show" '[.. | objects | select(.id? == $s)][0] | [.. | objects | select(.pane? != null)][0].pane')
[ "$first" = null ] || do_ pane.focus --pane "$first" >/dev/null
