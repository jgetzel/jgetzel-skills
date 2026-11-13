#!/bin/sh
# A made-up swarm for shot.sh: swarm/herdr/demo.sh DIR [away|back|dead|stale], then swarm/herdr/shot.sh --fixture DIR out.png.
# Writes DIR/swarm.db (a board mid-work: the limits reached, auto-spawn holding, a hung stayer, a blocked task),
# DIR/proc (the machine reading and `ps` output), DIR/bin/ps and DIR/state (a cmd-cost history for repo "demo").
# Variants: the user away, just back (the digest card), watchd dead or older than the code.
set -eu
[ $# -ge 1 ] || { echo "usage: swarm/herdr/demo.sh DIR [away|back|dead|stale]..." >&2; exit 2; }
here=$(cd -P "$(dirname "$0")" && pwd)
dir=$1; shift
away=0 watchd=1 started=0 back=
for v; do
  case $v in
    away) away=1 ;; back) away=1 back=1 ;; dead) watchd=2147483646 ;; stale) started=190 ;;
    *) echo "demo.sh: no variant $v" >&2; exit 2 ;;
  esac
done
mkdir -p "$dir/proc/pressure" "$dir/bin" "$dir/state/cmd-cost"
db=$dir/swarm.db
rm -f "$db" "$dir/state/cmd-cost/history.db"
# swarm-lean makes the board's schema
SWARM_DB=$db "$here/../swarm" board >/dev/null

# watchd's record: pid 1 stands for a live one (shot.sh makes it its own pid), 2147483646 for a dead one;
# "stale": started before the swarm code last changed. Times below are minutes before @now.
{
  echo ".parameter set @now $(date +%s)"
  echo ".parameter set @watchd '$watchd t3'"
  echo ".parameter set @started $started"
  echo ".parameter set @away $away"
  cat <<'SQL'
-- agents: ox-comms holds shot.sh's one terminal (t1): the header's Communicator link shows
insert into agent(name,model,status,last_active,ctx_tokens,role,stay,claude_pid,started,ended,snap,wt,hc) values
  ('ox-comms','opus','idle',@now-2*60,141000,'communicator','the user''s channel',100,@now-190*60,null,'{"files":[]}',null,'t1'),
  ('ox-1','opus','working',@now,236000,'implementer',null,110,@now-170*60,null,
    '{"files":["engine/src/plan.rs","engine/src/plan/cost.rs","engine/tests/plan.rs"]}','/work/atlas-ox-1',null),
  ('ox-2','opus','idle',@now-58*60,391000,'reviewer','PR reviews',120,@now-165*60,null,'{"files":[]}','/work/atlas-ox-2',null),
  ('ox-3','sonnet','idle',@now-6*60,88000,'implementer',null,130,@now-95*60,null,'{"files":["migrations/0042_tenants.sql"]}','/work/atlas-ox-3',null),
  ('ox-4','sonnet','idle',@now-21*60,64000,'CI watcher','main''s CI',140,@now-80*60,null,'{"files":[]}','/work/atlas-ox-4',null),
  ('ox-5','sonnet','working',@now,31000,null,null,150,@now-9*60,null,'{"files":["docs/plan-cache.md"]}','/work/atlas-ox-5',null),
  ('ox-6','sonnet','idle',@now-70*60,362000,null,null,null,@now-160*60,@now-70*60,'{"files":[]}',null,null),
  ('ox-7','opus','idle',@now-100*60,204000,null,null,null,@now-180*60,@now-100*60,'{"files":[]}',null,null);
insert into meta(k,v) values ('comms','ox-comms'), ('agent_min','5'), ('agent_max','5'),
  ('spawn_held','auto-spawn holding: 5 live, the auto-spawn number is 5; 2 task(s) startable; max 5'),
  ('watchd',@watchd),
  ('watchd_run','{"cwd":"/tmp","started":' || (@now-@started*60) || ',"flags":["--comms","ox-comms","--auto-spawn"]}');

-- tasks; the shots show the priority chips
insert into task(title,state,owner,created_by,evidence,deps,question,lease_until,model) values
  ('Planner: carry row estimates through joins','done','ox-7','ox-comms','PR #31 merged 4f2a9c1e',null,null,null,'sonnet'),
  ('Plan cache: key on the normalized query','done','ox-6','ox-comms','PR #33 merged 9be01d77',null,null,null,'sonnet'),
  ('Flaky test: plan_cache_evicts under load','done','ox-1','ox-2','PR #34 merged 1c3d5e7f, 40 runs green',null,null,null,'sonnet'),
  ('Planner: cost model for index scans','claimed','ox-1','ox-comms',null,null,null,@now+96*60,'sonnet'),
  ('Tenants: migration and backfill','blocked','ox-3','ox-comms',null,null,'Backfill in one transaction, or in batches of 10k?',@now+110*60,'sonnet'),
  ('Docs: how the plan cache is keyed','claimed','ox-5','ox-1',null,null,null,@now+112*60,'sonnet'),
  ('Planner: cost model for hash joins','open',null,'ox-1',null,null,null,null,'sonnet'),
  ('Bench: plan time on the 200-table schema','open',null,'ox-2',null,null,null,null,'sonnet'),
  ('Tenants: per-tenant plan cache','open',null,'ox-comms',null,'5',null,null,'sonnet'),
  ('Old: rewrite the parser','dropped',null,'ox-comms',null,null,null,null,'sonnet');
update task set priority=0 where title like 'Planner: cost model for hash%';
update task set priority=3 where title like 'Bench:%';
update task set priority=1 where title like 'Docs:%';

-- events, oldest first
insert into event(ts,agent,kind,path,data) values
  (@now-170*60,'ox-comms','spawn',null,'ox-1'), (@now-165*60,'ox-comms','spawn',null,'ox-2'),
  (@now-164*60,'ox-2','role',null,'reviewer'), (@now-163*60,'ox-2','stay',null,'PR reviews'),
  (@now-100*60,'ox-7','done',null,'#1 PR #31 merged 4f2a9c1e'), (@now-100*60,'ox-7','end',null,'landed'),
  (@now-95*60,'swarm','spawn',null,'auto #5'), (@now-94*60,'ox-3','claim',null,'#5'),
  (@now-80*60,'ox-comms','spawn',null,'ox-4'), (@now-79*60,'ox-4','stay',null,'main''s CI'),
  (@now-71*60,'ox-6','done',null,'#2 PR #33 merged 9be01d77'), (@now-70*60,'ox-6','end',null,'landed'),
  (@now-52*60,'ox-1','done',null,'#3 PR #34 merged 1c3d5e7f, 40 runs green'),
  (@now-50*60,'ox-1','claim',null,'#4'), (@now-44*60,'ox-1','task-add',null,'#7'), (@now-44*60,'ox-1','task-add',null,'#6'),
  (@now-38*60,null,'pressure',null,'machine: 3.9/31.3G mem available, pressure10 mem 14.2% cpu 61%'),
  (@now-31*60,null,'pressure-end',null,null),
  (@now-30*60,'ox-comms','limits',null,'min 5 max 5'),
  (@now-24*60,'ox-2','task-add',null,'#8'),
  (@now-20*60,'ox-4','stay-nowaiter',null,null),
  (@now-12*60,'ox-1','push','{"branch":"ox-1/index-scan-cost","subject":"planner: cost index scans by selectivity"}','git push'),
  (@now-9*60,'swarm','spawn',null,'auto #6'), (@now-9*60,'ox-5','claim',null,'#6'),
  (@now-8*60,'ox-2','stay-check',null,null),
  (@now-7*60,'ox-1','spawn-refused',null,'ox-8'),
  (@now-6*60,'ox-3','block',null,'#5 Backfill in one transaction, or in batches of 10k?'),
  (@now-5*60,'swarm','spawn-held',null,'auto-spawn holding: 5 live, the auto-spawn number is 5; 2 task(s) startable; max 5'),
  (@now-3*60,'ox-2','stay-hung',null,null);
insert into msg(ts,frm,dest,body,urgent,kind) values
  (@now-12*60,'ox-1','ox-2','PR #36 is ready: index scan costs. https://github.com/example/atlas/pull/36',0,'dm'),
  (@now-6*60,'swarm','ox-comms','ox-3 is blocked on #5: Backfill in one transaction, or in batches of 10k?',0,'system'),
  (@now-3*60,'swarm','ox-comms','ox-2 stays for ''PR reviews'' and did not answer the liveness check (terminal t12, hc status idle). Unstick it with `hc send`, or end it.',1,'system');

-- main's CI as watchd polled it, newest red
insert into ci(id,sha,status,conclusion,url,created,updated)
  select id, sha, 'completed', c, 'https://github.com/example/atlas/actions/runs/' || id,
    strftime('%Y-%m-%dT%H:%M:%SZ', @now-ago*60, 'unixepoch'), strftime('%Y-%m-%dT%H:%M:%SZ', @now-(ago-6)*60, 'unixepoch')
  from (select 9100412 id, 14 ago, 'failure' c, '5d02e6ab' sha union all select 9100377, 52, 'success', '1c3d5e7f'
    union all select 9100301, 71, 'success', '9be01d77' union all select 9100266, 100, 'success', '4f2a9c1e');

-- away, back: the user left an hour ago
insert into meta(k,v) select 'away', (@now-60*60) || ' lunch' where @away;
update task set done_at=@now-52*60, merged_at=@now-51*60, pr=34 where id=3 and @away;
insert into lock(path,agent,reason,since) values ('migrations/0042*','ox-3','tenants migration',@now-90*60);
SQL
} | sqlite3 "$db"
# back: and returned just now (the digest card)
[ -z "$back" ] || SWARM_DB=$db SWARM_NAME=human "$here/../swarm" away --back >/dev/null

# the machine: memory nearly short, and who holds it (pid ppid rss_kb etime time args)
printf 'MemTotal: 32823000 kB\nMemAvailable: 6100000 kB\n' >"$dir/proc/meminfo"
echo 'some avg10=4.20 avg60=0 avg300=0 total=0' >"$dir/proc/pressure/memory"
echo 'some avg10=38.50 avg60=0 avg300=0 total=0' >"$dir/proc/pressure/cpu"
cat >"$dir/proc/ps" <<'PS'
100 1 610000 190:00 2:10 claude
110 1 720000 170:00 9:40 claude
120 1 690000 165:00 7:02 claude
130 1 540000 95:00 3:31 claude
140 1 480000 80:00 1:12 claude
150 1 450000 9:00 0:40 claude
111 110 9437184 6:12 21:05 cargo test --release -p planner
112 110 1258291 6:12 2:00 rustc --crate-name planner
151 150 310000 1:05 0:12 node /x/bin/mdbook build
131 130 2202009 41:00 0:30 postgres -D /tmp/tenants
900 1 800000 300:00 4:00 claude
901 900 3355443 12:30 8:15 node /x/bin/vite build
PS
printf '#!/bin/sh\nexec cat "$SWARM_PROC/ps"\n' >"$dir/bin/ps"
chmod +x "$dir/bin/ps"

# the cmd-cost history of repo "demo" (shot.sh's demo repo), filed under this machine (cost.lean's schema and key)
{
  echo ".parameter set @now $(date +%s)"
  echo ".parameter set @machine '$(uname -n)'"
  cat <<'SQL'
create table cmd(id integer primary key, ts int, machine text, repo text, agent text, source text,
  cmd text, key text, wall_s int, cpu_s int, peak_kb int, exact int);
create index cmd_key on cmd(machine, repo, key, id);
insert into cmd(ts,machine,repo,agent,source,cmd,key,wall_s,cpu_s,peak_kb,exact) select @now-ago*60, @machine, 'demo', a,
    'swarm', c, k, w, cpu, kb, 0
  from (select 'ox-7' a, 'cargo test --release -p planner' c, 'cargo test --release' k, 410 w, 1880 cpu, 11744051 kb, 150 ago
    union all select 'ox-1', 'cargo test --release -p planner', 'cargo test --release', 372, 1790, 9856614, 61
    union all select 'ox-6', 'cargo build --release', 'cargo build --release', 245, 1310, 7130316, 120
    union all select 'ox-1', 'cargo bench --bench plan_time', 'cargo bench --bench', 905, 2400, 5033164, 75
    union all select 'ox-3', 'psql -f migrations/0042_tenants.sql', 'psql -f migrations/0042_tenants.sql', 188, 40, 2306867, 33
    union all select 'ox-1', 'cargo clippy --all-targets', 'cargo clippy --all-targets', 96, 420, 3460300, 14);
SQL
} | sqlite3 "$dir/state/cmd-cost/history.db"
echo "$dir"
