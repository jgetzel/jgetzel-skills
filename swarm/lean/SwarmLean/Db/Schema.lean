/-! The machine's db: its schema and which meta keys are the machine's (sw-global §2). -/

namespace SwarmLean

/-- The machine's schema (sw-global §2): every column inline, a fresh db (no migration of the per-repo dbs). -/
def schema : String := "
create table if not exists swarm(name text primary key, comms text, created int, ended int);
create table if not exists repo(path text primary key, base text);
create table if not exists swarm_repo(swarm text not null, repo text not null, primary key(swarm, repo));
create table if not exists task_repo(task int not null, repo text not null, base text, primary key(task, repo));
create table if not exists agent(name text primary key, swarm text, hc text, model text, cwd text, status text,
  last_active int, ctx_tokens int default 0, compacted_at int default 0, started int, ended int, snap text,
  waiter int, wt text, claude_pid int, role text, stay text);
create table if not exists msg(id integer primary key autoincrement, ts int, frm text, dest text,
  body text, urgent int default 0, kind text);
create table if not exists cursor(agent text primary key, last_msg_id int default 0);
create table if not exists task(id integer primary key autoincrement, title text, body text,
  state text default 'ready', owner text, lease_until int, created_by text, evidence text, deps text, model text, question text,
  effort text, created_at int, first_claimed_at int, done_at int, dropped_at int, pr int, merged_at int,
  ci_conclusion text, ci_green_at int, claim_ctx int, done_ctx int, answer text, base text, stop_to text, stop_msg int,
  priority int default 3, qpos int, hold text, labels text, parents text, land_sha text, lander text, landing_at int,
  dup_of int, parent int);
create table if not exists lock(repo text not null default '', path text not null, agent text, reason text, since int,
  lease_until int, seen int default 0, primary key(repo, path));
create table if not exists conflict(a text, b text, path text, since int, primary key(a,b,path));
create table if not exists pairkey(a text, b text, key text, primary key(a,b));
create table if not exists meta(scope text not null default '', k text not null, v text, primary key(scope, k));
create table if not exists event(id integer primary key autoincrement, ts int, swarm text, repo text, agent text,
  kind text, path text, data text);
create table if not exists workspace(repo text not null default '', path text, branch text, base text, agent text,
  ro int default 0, primary key(path, agent));
create table if not exists ci(repo text not null default '', id integer not null, sha text, status text, conclusion text,
  url text, created text, updated text, failed text, workflow text, primary key(repo, id));
create index if not exists agent_swarm on agent(swarm);
create index if not exists task_state on task(state);
create index if not exists task_repo_repo on task_repo(repo);
create index if not exists msg_dest on msg(dest, id);
create index if not exists event_swarm on event(swarm, id);
create index if not exists workspace_agent on workspace(agent);
create index if not exists lock_repo on lock(repo);
create index if not exists event_agent on event(agent, kind, id);
create index if not exists task_owner on task(owner);
create index if not exists event_kind on event(kind, ts);
create index if not exists event_swarm_agent on event(swarm, agent, id);
create index if not exists msg_frm on msg(frm, id);
"

/-- The invariant version of the db, stored in `pragma user_version` (a db header field: it is read and set in the same
transaction as the migration, needs no table, and a binary can read it before it knows the schema). A fresh or current
db is at the current version; a db made before the version existed reads 0 and is raised at connect.
Bump it, with an entry in `dbMigrations`, whenever `WF` or the schema changes: an older binary then refuses to write
(`Real.checkWritable`), so the "only our code writes" assumption under `wf_reach` (sw-global-proofs.md §3.7) holds across
binaries built at different commits. -/
def DB_VERSION : Nat := 4

/-- Version 2 (Linear's states): the task states renamed (open → ready, claimed → in_progress, blocked → needs_input,
landing → in_review, done → completed, dropped → cancelled); a held open task, and with a swarm's queue-only on an
unqueued open task of its repos, moves to backlog, its hold text kept as its note (column hold); every task not closed
gets a place (column qpos) in today's staffing order: the queue by place, then the rest by priority (NULL first) and
id; priorities move to Linear's numbers (P0 → 1 urgent … P3 → 4 low, NULL → 0 none); the queue-only knob goes; and
the task table is rebuilt so its column defaults are the new ones (state 'ready', priority 3), its autoincrement sequence
kept. Each statement is a no-op on an empty task table, so a fresh db (at version 0) runs it too. -/
def migrateV2 : List String := [
  "update task set state='backlog', hold=coalesce(hold, 'not queued (queue-only)') where state='open' and qpos is null \
    and exists (select 1 from task_repo tr join swarm_repo sr on sr.repo=tr.repo join meta m on m.scope=sr.swarm \
    and m.k='queue_only' and m.v='on' where tr.task=task.id)",
  "update task set state='backlog' where state='open' and hold is not null",
  "update task set qpos=(select rn from (select id, row_number() over (order by qpos is null, qpos, \
    priority is not null, priority, id) as rn from task where state not in ('done', 'dropped')) x where x.id=task.id) \
    where state not in ('done', 'dropped')",
  "update task set qpos=null where state in ('done', 'dropped')",
  "update task set state=case state when 'open' then 'ready' when 'claimed' then 'in_progress' \
    when 'blocked' then 'needs_input' when 'landing' then 'in_review' when 'done' then 'completed' \
    when 'dropped' then 'cancelled' else state end",
  "update task set priority=case when priority is null then 0 when priority<=0 then 1 when priority=1 then 2 \
    when priority=2 then 3 else 4 end",
  "delete from meta where k='queue_only'",
  "create table task_v2(id integer primary key autoincrement, title text, body text, \
    state text default 'ready', owner text, lease_until int, created_by text, evidence text, deps text, model text, \
    question text, effort text, created_at int, first_claimed_at int, done_at int, dropped_at int, pr int, merged_at int, \
    ci_conclusion text, ci_green_at int, claim_ctx int, done_ctx int, answer text, base text, stop_to text, stop_msg int, \
    priority int default 3, qpos int, hold text, labels text, parents text, land_sha text, lander text, landing_at int, \
    dup_of int)",
  "insert into task_v2(id, title, body, state, owner, lease_until, created_by, evidence, deps, model, question, effort, created_at, first_claimed_at, done_at, dropped_at, pr, merged_at, ci_conclusion, ci_green_at, claim_ctx, done_ctx, answer, base, stop_to, stop_msg, priority, qpos, hold, labels, parents, land_sha, lander, landing_at, dup_of) \
    select id, title, body, state, owner, lease_until, created_by, evidence, deps, model, question, effort, created_at, first_claimed_at, done_at, dropped_at, pr, merged_at, ci_conclusion, ci_green_at, claim_ctx, done_ctx, answer, base, stop_to, stop_msg, priority, qpos, hold, labels, parents, land_sha, lander, landing_at, dup_of from task",
  "update sqlite_sequence set seq=max(seq, coalesce((select seq from sqlite_sequence where name='task'), 0)) \
    where name='task_v2'",
  "drop table task",
  "alter table task_v2 rename to task",
  "create index if not exists task_state on task(state)",
  "create index if not exists task_owner on task(owner)"]

/-- Version 3 (sub-issues): the task's goal parent (column parent, NULL: top level) and an index on it. The column is
not in `columns`: version 2's rebuild of the task table leaves it out, so only this migration may add it. A db made at
version 2 has no such column until it runs. -/
def migrateV3 : List String := [
  "alter table task add column parent int",
  "create index if not exists task_parent on task(parent)"]

/-- Version 4 (Proposed): the task state `proposed`, an unstarted state beside Backlog that an agent's `task add` files in. No
statement: the column is text and every state is a value of it, but a binary from before version 4 reads `proposed` as
no state, so it must refuse the db (`Real.checkWritable`) once a newer binary has connected. -/
def migrateV4 : List String := []

/-- The migrations: `(v, sqls)` takes a db at version `v - 1` to `v`, run in order by `connect` in one BEGIN IMMEDIATE.
Obligation (for the proofs phase): if `WF_{v-1} db` then `WF_v` holds of the db after `sqls`, where `WF_v` is `WF` at
the commit that bumped `DB_VERSION` to `v`. -/
def dbMigrations : List (Nat × List String) := [(2, migrateV2), (3, migrateV3), (4, migrateV4)]

/-- The meta keys of the machine (scope `''`); every other key is a swarm's (scope: its name). -/
def machineKeys : List String := ["watchd", "watchd_tick", "watchd_up", "watchd_run", "machines", "jobs"]

/-- The meta scope of key `k` in swarm `s`. -/
def metaScope (s k : String) : String := if machineKeys.contains k then "" else s

end SwarmLean
