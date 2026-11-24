#!/bin/sh
# Made-up spaces, agents and shells for screenshots of the rework (rw-* mods), then the rework layout. Run inside
# shot.sh's sandbox, never in the person's window; shot.sh --rework <preset> runs it:
#   swarm/herdr/shot.sh --rework real|large|small out.png
#   swarm/herdr/shot.sh --before 'sh swarm/herdr/rail-demo.sh [--preset P] [--fold] [--swarm 5|24 [--two]] [--vps]' out.png
# Presets (no flags: real):
# - real: about the user's window. Ten spaces on this computer, 15 agents. Two swarms shaped as `swarm spawn` makes them:
#   jgetzel-skills' communicator ll-comms joined in its space (its terminal's swarm label), the machine's one
#   watchd (a terminal with no pane), workers started with
#   --outlive-parent from the communicator's terminal, from watchd's (auto-spawn) or from an earlier communicator's
#   that has ended; one asks, one is hung, one has a helper, four ended. high-perf-lean runs hpl, one of them asking.
#   As in the user's window (#175), the spaces' folders are off: jgetzel-skills' is the home folder, high-perf-lean's
#   the jgetzel-skills repo. Plain spaces hold agents, a sub-agent, codex and shells. "desktop" has spaces of the same
#   names; "vps" is unreachable.
# - large: real, with jgetzel-skills at 24 live agents and 110 ended.
# - small: the rail's first demo; with no other flag no swarm, else as the flags say.
# - hostile: large, plus a space "hostile" (#180) whose name breaks a line, reverses text and runs 300 characters, an agent
#   whose title says "asks you" while it works, a tab named in RTL, zero-width and combining text, 300 shell tabs, and in
#   jgetzel-skills a task whose title breaks lines and runs 600 characters, its question starting with a dash.
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
hostile=; [ "$preset" != hostile ] || { hostile=1 preset=large; }
case $preset in small|real|large) ;; *) echo "rail-demo.sh: no preset $preset (small, real, large, hostile)" >&2; exit 2 ;; esac
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

# A swarm (sw-global): a group of agents in the machine's one db, made by `swarm new`, with a repo its tasks belong to;
# each fake agent records its own terminal. The helpers below write to $db for swarm $cur (repo $crepo) as they run.
now=$(date +%s)
db=${XDG_STATE_HOME:?shot.sh sets it}/swarm/swarm.db
sql() { sqlite3 -cmd ".timeout 9000" "$db" "$@"; }
# board <repo> <comms> <min> <max>: a git repo and the swarm <comms> leads (named <comms> less -comms), no tasks; sets
# cur and crepo
board() {
  git -C "$1" init -q
  cur=${2%-comms}
  (cd "$1" && env -u SWARM_NAME "$D/swarm" new "$cur" --repo "$1" && SWARM_NAME=human "$D/swarm" --swarm "$cur" limits --min "$3" --max "$4") >/dev/null 2>&1
  crepo=$(sql "select repo from swarm_repo where swarm='$cur' limit 1")
  sql "update swarm set comms='$2' where name='$cur'"
}
cat >"$(dir .)/reg.sh" <<'EOF'
sqlite3 -cmd ".timeout 9000" "$1" "insert or replace into agent(name, swarm, hc, status, last_active, started, stay, claude_pid) values('$2', '$6', '$HC_TERMINAL_ID', '$3', $4, 1, nullif('$5', ''), $PPID);
  insert or replace into workspace(repo, path, agent) values('$7', '$PWD', '$2')"
EOF
# swagent <name> <db status> <seconds idle> <stay> <agent args...>: a fake agent that registers in $cur (its workspace in
# $crepo, as `swarm spawn` records one), then as agent()
swagent() {
  n=$1 st=$2 ago=$3 stay=$4; shift 4
  jq -cn --arg c "sh '$D/w/reg.sh' '$db' '$n' '$st' $((now - ago)) '$stay' '$cur' '$crepo'; $(agent "$@" | jq -r '.[2]')" '["sh","-c",$c]'
}
# task <id> <title> <state> [owner] [question]: a task of $crepo (state: in_progress, needs_input, ready, ...; a Ready or Backlog one's place is its id)
task() { sql "insert into task(id, title, state, owner, question, qpos, lease_until) values($1, '$2', '$3', nullif('${4:-}', ''), nullif('${5:-}', ''),
    case when '$3' in ('ready', 'backlog') then $1 end, case when '$3' in ('in_progress', 'needs_input') then $((now + 5400)) end);
  insert into task_repo(task, repo) values($1, '$crepo')"; }
# homed: the tasks with no repo yet (the bulk inserts') are $crepo's
homed() { sql "insert into task_repo(task, repo) select id, '$crepo' from task where id not in (select task from task_repo)"; }
# ev <ts> <agent> <kind>: an event of $cur's
ev() { sql "insert into event(ts, swarm, agent, kind, data) values($1, '$cur', '$2', '$3', '')"; }
# wtab <space> <communicator's terminal> <argv>: a worker started from the communicator's terminal (so that is its
# parent), opting into the space; Herdr gives it a tab there.
wtab() { hc run --bg --json --parent "$2" --label "herdr.space=$1" -- sh -c "$(echo "$3" | jq -r '.[2]')" >/dev/null; }
# spawn <parent terminal> <space> <swagent args...>: a worker as `swarm spawn` starts one (launch.sh): named, in its
# worktree, outliving its parent, opting into the swarm's space
spawn() {
  p=$1 s=$2 wt=$(dir "$(basename "$crepo")-$3"); shift 2
  hc run --bg --json --parent "$p" --outlive-parent --no-notify --name "$1" --cwd "$wt" --label "herdr.space=$s" -- sh -c "$(swagent "$@" | jq -r '.[2]')" >/dev/null
}
# join <space> <terminal>: what `swarm join` records for a communicator: its terminal's swarm label (board sets the
# swarm row's comms)
join() { hc label "$2" "swarm=$cur" >/dev/null; }
# watchd <repo>: the machine's one watchd as `swarm watchd --restart` starts it, a terminal with no parent and so no
# pane; sets wd (its terminal)
watchd() {
  wd=$(hc run --bg --json --no-parent --no-notify --cwd "$1" -- sh -c "echo \$\$ >'$1/.git/watchd.pid'; exec sleep 1d" | id address)
  until [ -s "$1/.git/watchd.pid" ]; do sleep 0.2; done
  sql "insert or replace into meta(scope, k, v) values('', 'watchd', '$(cat "$1/.git/watchd.pid") $wd')"
}
# rich: the swarm's tasks for every board view (Linear states): In Progress (an agent's, human's), In Review with a PR, Ready with
# a dependency on an in-progress and on a cancelled task, a reserved task and every priority, Backlog with notes, Completed,
# Cancelled with notes, Duplicates; the CLI's own verbs write the events (task backlog/ready/assign/priority/drop/queue). Tasks
# 133, 146, 145 and 142 are the agents' own (needs input and in progress).
rich() {
  cli() { (cd "$crepo" && SWARM_NAME=${who:-human} "$D/swarm" --swarm "$cur" "$@") >/dev/null; }
  # tk <id> <title> <state> <priority> <qpos|-> [owner] [label]
  tk() { sql "insert into task(id, title, body, state, priority, qpos, owner, labels, created_at, created_by) values($1, '$2', '', '$3', $4, nullif('$5', '-'),
      nullif('${6:-}', ''), nullif('${7:-}', ''), $((now - 86400 * 3)), 'll-comms'); insert into task_repo(task, repo) values($1, '$crepo')"; }
  sql "delete from task where id in (150, 151); delete from task_repo where task in (150, 151)"
  tk 1812 'Board rows from TaskState' in_progress 2 - ll-110 rw-swarm
  tk 1813 'queue add moves the position only' in_progress 3 - human cli
  tk 1809 'SafeTxn wrapper for the store' in_review 3 - ll-127 lean
  sql "update task set pr = 521, done_at = $((now - 600)), first_claimed_at = $((now - 5000)), land_sha = 'bea333c', landing_at = $((now - 600)) where id = 1809;
    update task set lease_until = $((now + 6000)) where id in (1812, 1813);
    update task set first_claimed_at = $((now - 2500)) where id = 1812;  update task set first_claimed_at = $((now - 1080)) where id = 1813"
  tk 1814 'Verbs: task backlog, task ready' ready 2 1 '' cli
  tk 1815 'Priority names in the CLI' ready 3 2 '' cli
  tk 1816 'Duplicate links to its original' ready 4 3 '' cli
  tk 1817 'Staffing line wording in rw-rail' ready 0 4 '' rw-rail
  tk 1803 'Lease expiry is off by one second' ready 1 5 '' watchd
  tk 1818 'Category filter in rw-swarm' ready 3 6 '' rw-swarm
  tk 1819 'Graph view colours by category' ready 3 7 '' rw-swarm
  tk 1820 'Lean store spike' ready 3 8 '' lean
  tk 1821 '"Duplicate of" in task show' ready 3 9 '' cli
  tk 1806 'Place the calendar in the rail' ready 2 20
  tk 1801 'Slurm compute claims' ready 2 21
  tk 1799 'Blur through XWayland' ready 0 22
  tk 1822 'Lean store for tasks' ready 2 23
  tk 1823 'Task templates' ready 3 24 '' cli
  tk 1810 'Task state carries its data' completed 2 - ll-97 lean
  tk 1807 'Spawned tab opens in the swarm''s space' completed 3 - ll-110
  tk 1804 'Claim test flakes on main' completed 1 - ll-124
  tk 1802 'lean-sqlite theorem list' completed 3 - ll-125
  tk 1798 'Category column in Rows.lean' ready 3 25
  tk 1795 'Proofs over the Lua CLI' ready 3 26
  tk 1790 'Pills shrink to fit the bar' ready 0 27
  tk 1811 'Task state enum in Rows.lean' ready 3 28
  tk 1797 'Graph view of the queue' ready 4 29
  sql "update task set pr = 518, done_at = $((now - 7200)) where id = 1810; update task set pr = 517, done_at = $((now - 3600 * 5)) where id = 1807;
    update task set pr = 515, done_at = $((now - 86400)) where id = 1804; update task set pr = 519, done_at = $((now - 90000)) where id = 1802"
  # the CLI's verbs: Backlog with notes, then the rest
  cli task backlog 1806 --note 'Waits for your go'
  cli task backlog 1801 --note 'Only if there is no Mac'
  cli task backlog 1799 --note 'Parked in round 2'
  cli task backlog 1822 --note 'Waits on the Lean store spike'
  cli task backlog 1823 --note 'After the verbs land'
  cli task after 1815 1813; cli task after 1818 1798; cli task after 1819 1818; cli task after 1821 1815
  cli task assign 1820 human
  cli task backlog 1821 --note 'After the task show output settles'; cli task ready 1821
  cli queue add 1814 --after 1817; cli queue add 1814 --front
  cli task priority 1815 low; cli task priority 1815 medium; cli task priority 1816 low
  cli task drop 1798 --note 'Folded into #1812'
  cli task drop 1795 --note 'Lean port first'
  cli task drop 1790 --note 'Tabs moved to the rail'
  cli task drop 1811 --duplicate-of 1810
  cli task drop 1797 --duplicate-of 1802
  sql "update event set agent = 'll-comms' where data like '#1806%' or data like '#1798%' or data like '#1790%' or data like '#1811%' and kind != 'task-place'"
  sql "update task set model = case id when 1803 then 'opus' when 1820 then 'opus' when 1821 then 'haiku' else 'sonnet' end where id in (1814, 1815, 1816, 1817, 1803, 1818, 1819, 1820, 1821)"
  cli limits --min 7 --max 8
  ev $((now - 90)) ll-107 stay-hung
  sql "update task set dropped_at = case id when 1798 then $((now - 1200)) when 1795 then $((now - 86400 * 3)) when 1790 then $((now - 86400 * 6)) when 1811 then $((now - 7000)) else $((now - 86400 * 4)) end where state in ('cancelled', 'duplicate')"
  # ages: the event times the screenshot reads
  sql "update event set ts = $((now - 3600 * 48)) where kind = 'task-backlog' and data like '#1806%';
    update event set ts = $((now - 120)) where kind = 'task-ready'; update event set ts = $((now - 180)) where kind = 'task-backlog' and data like '#1821%';
    update event set ts = $((now - 2400)) where kind = 'task-place' and data like '#1814 4%'; update event set ts = $((now - 2700)) where kind = 'task-place' and data like '#1814 1 4%';
    update event set ts = $((now - 9000)) where kind = 'task-priority' and data like '#1815 low%'; update event set ts = $((now - 2280)) where kind = 'task-priority' and data like '#1815 medium%';
    update event set ts = $((now - 1200)) where kind = 'drop' and data like '#1798%'; update event set ts = $((now - 86400 * 3)) where kind = 'drop' and data like '#1795%';
    update event set ts = $((now - 86400 * 6)) where kind = 'drop' and data like '#1790%'; update event set ts = $((now - 7000)) where kind = 'task-duplicate' or (kind = 'drop' and (data = '#1811' or data = '#1797'));
    update event set ts = $((now - 4000)) + id * 25 where ts >= $((now - 30)) and (kind like 'task-%' or kind = 'limits')"
}
# await <n>: until n of $cur's agents are live, each having recorded its terminal
await() {
  n=0; while [ $n -lt 30 ] && [ "$(sql "select count(*) from agent where ended is null and swarm='$cur'")" -lt "$1" ]; do sleep 1; n=$((n + 1)); done
}

show=
if [ "$preset" != small ]; then
  # jgetzel-skills: ll-comms in a space whose folder is the home folder (#175); some workers spawned by ll-comms, some
  # by watchd, one by an earlier ll-comms whose terminal has ended. Agents title themselves with their name.
  repo=$(dir jgetzel-skills); board "$repo" ll-comms 0 6; llrepo=$crepo
  made=$(do_ space.new --name jgetzel-skills --folder "$(dir jgetzel)" --argv "$(swagent ll-comms idle 120 '' done ll-comms)")
  show=$(echo "$made" | id space) llc=$(echo "$made" | id terminal)
  join "$show" "$llc"; watchd "$repo"
  spawn "$llc" "$show" ll-124 working 0 '' working ll-124 'explore-124|working|find the live shots in GAPS.md'
  task 179 'Herdr rework: make the screenshot sandbox match a real setup (real-shaped swarms, second machine, size presets)' in_progress ll-124
  spawn "$wd" "$show" ll-125 working 0 '' idle ll-125
  task 180 'Herdr rework: hardening against hostile input and arbitrary scale (sessions, tabs, swarms)' needs_input ll-125 \
    'A rail of 300 terminals takes 2 s to draw. Cap it at 200 rows with a "more" line, or page it?'
  old=$(hc run --bg --json --no-parent --no-notify -- sh -c 'sleep 2' | id address)
  spawn "$old" "$show" ll-126 idle 3480 reviews idle ll-126
  task 171 'watchd: after a compaction, a staying agent or the communicator gets no continue prompt' in_progress ll-126
  ev $((now - 60)) ll-126 stay-hung
  spawn "$llc" "$show" ll-127 idle 1500 '' done ll-127
  task 170 'Crash safety: fix the four stop-between-steps leaks #133 found (F1, F2, F3, F5)' in_progress ll-127
  live=5
  if [ "$preset" = large ]; then # 19 more, auto-spawned by watchd
    i=130; while [ $i -le 148 ]; do
      st=working; [ $((i % 4)) != 0 ] || st=idle
      spawn "$wd" "$show" ll-$i $st 0 '' $st ll-$i; task $((i + 1000)) "Task $i" in_progress ll-$i; i=$((i + 1))
    done
    sql "with recursive n(i) as (select 1 union all select i + 1 from n where i < 31) insert into task(id, title, state, priority, qpos)
      select 2000 + i, 'Later '||i, 'ready', i % 3 + 2, 2000 + i from n"
    live=24
  fi
  sql "with recursive n(i) as (select 1 union all select i + 1 from n where i < $((live == 24 ? 110 : 4)))
    insert into agent(name, swarm, hc, status, last_active, started, ended, model, wt) select 'll-'||(124 - i), 'll', 'tx'||i, 'idle',
    $now - i * 900, $now - i * 900 - 5400, $now - i * 900, 'opus', '/w/jgetzel-skills-ll-'||(124 - i) from n;
    insert into task(id, title, state, owner) values(173, 'Herdr rework: visual gap audit of the build against the canvas', 'completed', 'll-120'),
    (174, 'Herdr rework look A: the canvas''s warm palette as the rework layout''s theme', 'completed', 'll-121'),
    (175, 'Herdr rework: the live rail draws no swarm block', 'completed', 'll-122'), (177, 'Herdr rework look D', 'completed', 'll-123'),
    (167, 'Phone app (.apk) to view and message remote agents over hc connect', 'backlog', null),
    (181, 'swarm board: group done tasks by day', 'ready', null);
    update task set qpos = 1000, hold = 'waits for the user''s go' where id = 167; update task set qpos = 1001 where id = 181;
    insert into msg(ts, frm, dest, body, kind) values($((now - 2400)), 'll-127', 'll-comms', 'PR #342 is ready.', 'dm'),
    ($((now - 300)), 'll-comms', 'll-124', 'Use the real preset for the before/after check.', 'dm');
    insert into ci(repo, id, sha, status, conclusion, url, created, workflow) values('$crepo', 1, 'bea333c', 'completed', 'success', '', '$(date -u +%Y-%m-%dT%H:%M:%SZ)', 'swarm-lean')"
  homed
  tab "$show" '["zsh"]'
  await "$live" # reg.sh replaces a row: models and context sizes once all have
  sql "update agent set model = case cast(substr(name, 4) as int) % 3 when 0 then 'opus' when 1 then 'sonnet' else 'fable' end,
    ctx_tokens = 40000 + cast(substr(name, 4) as int) % 9 * 31000 where ended is null and swarm = 'll' and name != 'll-comms'"
  # high-perf-lean: hpl, in a space whose folder is the jgetzel-skills repo (#175)
  board "$(dir high-perf-lean)" hpl-comms 3 3
  made=$(do_ space.new --name high-perf-lean --folder "$repo" --argv "$(swagent hpl-comms idle 300 '' idle hpl-comms)")
  hpl=$(echo "$made" | id space) hplc=$(echo "$made" | id terminal)
  join "$hpl" "$hplc"
  spawn "$hplc" "$hpl" hpl-3 working 0 '' working hpl-3; task 41 'Arena allocator for Expr' in_progress hpl-3
  spawn "$wd" "$hpl" hpl-4 idle 1140 '' idle hpl-4; task 44 'Bench: Mathlib import time' needs_input hpl-4 \
    'The Mathlib import bench needs 40 G for 25 minutes. Run it now, or wait until the ll swarm is quieter?'
  task 49 'Inline small closures in the compiler pass' ready
  sql "insert into ci(repo, id, sha, status, conclusion, url, created, workflow) values('$crepo', 1, 'a1b2c3d', 'in_progress', null, '', '$(date -u +%Y-%m-%dT%H:%M:%SZ)', 'ci')"
  await 3; cur=ll crepo=$llrepo
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

if [ -n "$hostile" ]; then
  long=$(printf '%0300d' 0 | tr 0 x)
  ho=$(do_ space.new --name "$(printf 'evil\nname \342\200\256desrever\342\200\254 %s' "$long")" --folder "$(dir hostile)" \
    --argv "$(agent working 'asks you')" | id space)
  tab "$ho" "$(agent idle "$(printf 'two\\nlines \342\200\213\342\200\213 bidi \342\200\256gnol')")"
  hn=$(herdr-app ls | jq -r --arg s "$ho" '.spaces[] | select(.id == $s) | .tabs[-1].id')
  do_ tab.rename --id "$hn" --name "$(printf 'مرحبا \342\200\213 👨‍👩‍👧 Z\314\267\314\241\314\233\314\244a\314\265l\314\264g\314\266o')" >/dev/null
  i=0; while [ $i -lt 300 ]; do do_ tab.new --space "$ho" --argv '["sh","-c","exec sleep 1d"]' >/dev/null; i=$((i + 1)); done
  sql "update task set title = 'Line one
line two: $long$long', question = '-1 or --force? Answer with a dash.' where id = 180"
fi

folds=; [ -z "$fold" ] || folds="$jk $nix $linn"
if [ -n "$sw" ]; then
  repo=$(dir jgetzel-skills); board "$repo" ll-comms 0 99
  made=$(do_ space.new --name jgetzel-skills --folder "$repo" --argv "$(swagent ll-comms idle 120 '' done ll-comms)")
  skills=$(echo "$made" | id space) llc=$(echo "$made" | id terminal) show=$skills
  if [ "$sw" = 5 ]; then
    wtab "$skills" "$llc" "$(swagent ll-97 working 0 '' idle ll-97)"; task 133 'Lean proofs: crash safety between any two steps' needs_input ll-97 'Spawn.unreserve ends the row but keeps its locks. Fix it in this PR, or as its own task?'
    wtab "$skills" "$llc" "$(swagent ll-110 working 0 '' working ll-110 'research|working|read the mod guide')"; task 146 'Rail swarm block' in_progress ll-110
    wtab "$skills" "$llc" "$(swagent ll-111 working 0 '' working ll-111)"; task 145 'Bar pills' in_progress ll-111
    wtab "$skills" "$llc" "$(swagent ll-107 idle 3660 '' done ll-107)"; task 142 'Pane cards' in_progress ll-107
    task 150 'Collapsed rail' ready; task 151 'Settings' ready
    rich
    folds="$nix $linn"
  else
    wtab "$skills" "$llc" "$(swagent ll-203 working 0 '' idle ll-203)"; task 214 'Swarm tab' needs_input ll-203 'Keep the old panel?'
    wtab "$skills" "$llc" "$(swagent ll-205 working 0 '' idle ll-205)"; task 231 'Machines' needs_input ll-205 'Which machine is the vps?'
    wtab "$skills" "$llc" "$(swagent ll-209 idle 3480 reviews idle ll-209)"; task 222 'Review queue' in_progress ll-209
    ev $((now - 60)) ll-209 stay-hung
    i=210; while [ $i -le 223 ]; do # 14 working, ll-211 among them (you opened it)
      wtab "$skills" "$llc" "$(swagent ll-$i working 0 '' working ll-$i)"; task $((i + 1000)) "Task $i" in_progress ll-$i; i=$((i + 1))
    done
    for i in 224 225 226 227 228 229; do wtab "$skills" "$llc" "$(swagent ll-$i idle 1800 '' done ll-$i)"; done
    sqlite3 -cmd ".timeout 9000" "$db" "with recursive n(i) as (select 1 union all select i + 1 from n where i < 31) insert into task(id, title, state, qpos) select 2000 + i, 'Later '||i, 'ready', 2000 + i from n"
    homed
    folds="$jk $nix $linn"
  fi
  tab "$skills" "$(agent working 'read the watchd log')"
  tab "$skills" '["zsh"]'
  if [ -n "$two" ]; then # hpl: swagent and task write to $db as they run
    llrepo=$crepo hrepo=$(dir high-perf-lean); board "$hrepo" hpl-comms 8 8
    made=$(do_ space.new --name high-perf-lean --folder "$hrepo" --argv "$(swagent hpl-comms idle 300 '' idle hpl-comms)")
    hpl=$(echo "$made" | id space) hplc=$(echo "$made" | id terminal)
    wtab "$hpl" "$hplc" "$(swagent hpl-4 idle 1140 '' idle hpl-4)"; task 44 'Bench: Mathlib import time' needs_input hpl-4 'The Mathlib import bench needs 40 G for 25 minutes. Run it now, or wait until the ll swarm is quieter?'
    wtab "$hpl" "$hplc" "$(swagent hpl-3 working 0 '' working hpl-3)"; task 41 'Arena allocator for Expr' in_progress hpl-3
    wtab "$hpl" "$hplc" "$(swagent hpl-6 working 0 '' working hpl-6)"; task 45 'Simp cache keyed by pointer hash' in_progress hpl-6
    wtab "$hpl" "$hplc" "$(swagent hpl-7 idle 540 '' idle hpl-7)"; task 47 'CI: perf regression gate' in_progress hpl-7
    task 49 'Inline small closures in the compiler pass' ready; task 50 'Bench: instantiateMVars on deep terms' ready
    sqlite3 -cmd ".timeout 9000" "$db" "insert into ci(repo, id, sha, status, conclusion, url, created, workflow) values('$crepo', 1, 'a1b2c3d', 'in_progress', null, '', '$(date -u +%Y-%m-%dT%H:%M:%SZ)', 'ci')"
    cur=ll crepo=$llrepo
  fi
fi

# "desktop": spaces named like this computer's, with shells. Its compute ledger and reading are its own (compute-demo.sh
# fills the ledger): 16 cores, 15 of them busy (a counter that advances while the sandbox lives), 64 G, 40 G available.
ds=${HC_SESSION}d dk=$D/w/desktop
mkdir -p "$dk"
printf 'MemTotal: 67108864 kB\nMemAvailable: 41943040 kB\n' >"$dk/meminfo"
(u=0 i=0; while [ -d "$HERDR_APP_HOME" ]; do u=$((u + 15)) i=$((i + 1))
  { echo "cpu  $u 0 0 $i 0 0 0 0 0 0"; for c in 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15; do echo "cpu$c 0 0 0 0 0 0 0 0 0 0"; done; } >"$dk/stat.new"
  mv "$dk/stat.new" "$dk/stat"; sleep 0.1; done) >/dev/null 2>&1 &
hc machine add --via "env SWARM_COMPUTE_DIR=$dk/compute SWARM_COMPUTE_STAT=$dk/stat SWARM_COMPUTE_MEM=$dk/meminfo sh -c" --name desktop --session "$ds" >/dev/null
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
  insert into ci(repo, id, sha, status, conclusion, url, created, workflow) values('$crepo', 1, '08cc4a8', 'completed', 'success', '', '$(date -u +%Y-%m-%dT%H:%M:%SZ)', 'swarm-lean');
  update task set lease_until = $((now + 5280)), first_claimed_at = $((now - 15360)) where id = 133;
  update agent set status = 'idle', last_active = $((now - 360)), snap = '{\"files\":[\"swarm/lean/SwarmLean/Proofs/Crash.lean\",
    \"swarm/lean/SwarmLean/Proofs/Watchd.lean\",\"swarm/lean/SwarmLean/Db/Spawn.lean\",\"swarm/lean/SwarmLean/Lib/Spawn.lean\",
    \"swarm/lean/SwarmLean/Lib/Conflict.lean\",\"swarm/lean/SwarmLean/Cmd/State.lean\"]}' where name = 'll-97';
  insert into event(ts, swarm, agent, kind, data) values($((now - 9000)), 'll', 'll-97', 'compact', '')"
# The large swarm's table and board: models, 12 ended agents, the next tasks' priorities.
[ "$sw" != 24 ] || sqlite3 -cmd ".timeout 9000" "$db" "update agent set model = case cast(substr(name, 4) as int) % 3 when 0 then 'opus'
  when 1 then 'sonnet' else 'fable' end, ctx_tokens = 40000 + cast(substr(name, 4) as int) % 9 * 31000 where swarm = 'll' and name != 'll-comms';
  with recursive n(i) as (select 1 union all select i + 1 from n where i < 12) insert into agent(name, swarm, hc, status, last_active, started,
  ended, model, wt) select 'll-'||(180 + i), 'll', 'tx'||i, 'idle', $now - i * 1500, $now - i * 1500 - 5400, $now - i * 1500, 'opus',
  '/w/jgetzel-skills-ll-'||(180 + i) from n;
  update task set priority = (id % 3) + 2 where id > 2000"
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
