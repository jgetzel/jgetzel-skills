# cmd-cost history

One SQLite file per user and machine: `$XDG_STATE_HOME/cmd-cost/history.db` (default `~/.local/state/cmd-cost/history.db`).
It belongs to commands on a machine, not to a swarm, so any tool may write it. watchd writes `source='swarm'` rows (the
Bash-tool shells of agents, and `user:<name>` for the user's own claude sessions in this repo's worktrees; measured only);
`swarm run --on` writes `source='run'`; a repo's own build script may write `source='repo'`, `exact=1`.

```sql
create table cmd(id integer primary key, ts int, machine text, repo text, agent text, source text,
  cmd text, key text, wall_s int, cpu_s int, peak_kb int, exact int);
create index cmd_key on cmd(machine, repo, key, id);
create index cmd_rk on cmd(repo, key, id);
```

- `key`: the command without a leading `cd … &&`, `swarm run … --`, `VAR=x`, or trailing pipes and redirections, cut to its first three words.
- A row is written when `wall_s >= 60` or `peak_kb >= 1 GiB`, except a `source='run'` row, which `swarm run` writes for
  every job it runs, here and on another machine, with no threshold (a local job's `cpu_s` and `peak_kb` are 0: watchd
  measures the agent's command). A `run` row is keyed by the user's command, whatever `run.prefix` wraps it in. Nothing is
  pruned: every row stays, for later analysis (about 150 bytes a row).
- The window: `swarm run` reads the newest 50 rows of this repo and key from any machine (`cmd_rk` serves it), and the
  machine note and `swarm cost "<command>"` the newest 50 for this machine. `swarm cost --top` reads every row. So
  `swarm cost` and the note include short jobs now.
- The estimate (`swarm run`'s expected wall time, which backfill uses: sw-compute-backfill.md §2): the nearest-rank 90th
  percentile of the window's `run` rows with `wall_s > 0` (the ⌈0.9 n⌉-th of the sorted walls; under 10 rows, the largest);
  none without such a row. Wall time depends on the cores a job got and the history does not record them.
- `exact=0`: peak is the largest RSS sum of the command's process tree over watchd's 30 s samples (it can run low).
- `exact=1`: the peak is the agent's cgroup `memory.peak` (the agent runs in a `swarm-agent-*` scope where a systemd user session exists), taken when it rose while this was the agent's only open command. It includes the claude process itself.

A repo script's row, from shell:

```sh
sqlite3 "${XDG_STATE_HOME:-$HOME/.local/state}/cmd-cost/history.db" "insert into cmd(ts,machine,repo,agent,source,cmd,key,wall_s,cpu_s,peak_kb,exact) values(strftime('%s','now'),'$(hostname)','myrepo','$SWARM_NAME','repo','just build','just build',$wall,$cpu,$peak_kb,1)"
```

Read it with `swarm cost "<command>"` and `swarm cost --top [--repo R | --all-repos]`.
