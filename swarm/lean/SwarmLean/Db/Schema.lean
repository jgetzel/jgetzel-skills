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
  state text default 'open', owner text, lease_until int, created_by text, evidence text, deps text, model text, question text,
  effort text, created_at int, first_claimed_at int, done_at int, dropped_at int, pr int, merged_at int,
  ci_conclusion text, ci_green_at int, claim_ctx int, done_ctx int, answer text, base text, stop_to text, stop_msg int,
  priority int default 2, qpos int, hold text, labels text, parents text, land_sha text, lander text, landing_at int);
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
"

/-- The meta keys of the machine (scope `''`); every other key is a swarm's (scope: its name). -/
def machineKeys : List String := ["watchd", "watchd_tick", "watchd_up", "watchd_run", "machines", "jobs"]

/-- The meta scope of key `k` in swarm `s`. -/
def metaScope (s k : String) : String := if machineKeys.contains k then "" else s

end SwarmLean
