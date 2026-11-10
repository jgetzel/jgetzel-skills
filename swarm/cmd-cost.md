# cmd-cost history

One SQLite file per user and machine: `$XDG_STATE_HOME/cmd-cost/history.db` (default `~/.local/state/cmd-cost/history.db`).
It belongs to commands on a machine, not to a swarm, so any tool may write it. watchd writes `source='swarm'` rows (the
Bash-tool shells of agents, and `user:<name>` for the user's own claude sessions in this repo's worktrees; measured only);
`swarm run --on` writes `source='run'`; a repo's own build script may write `source='repo'`, `exact=1`.

```sql
create table cmd(id integer primary key, ts int, machine text, repo text, agent text, source text,
  cmd text, key text, wall_s int, cpu_s int, peak_kb int, exact int);
create index cmd_key on cmd(machine, repo, key, id);
```

- `key`: the command without a leading `cd … &&`, `swarm run … --`, `VAR=x`, or trailing pipes and redirections, cut to its first three words.
- A row is written only when `wall_s >= 60` or `peak_kb >= 1 GiB`. Keep the newest 20 per `(machine, repo, key)`.
- `exact=0`: peak is the largest RSS sum of the command's process tree over watchd's 30 s samples (it can run low).

A repo script's row, from shell:

```sh
sqlite3 "${XDG_STATE_HOME:-$HOME/.local/state}/cmd-cost/history.db" "insert into cmd(ts,machine,repo,agent,source,cmd,key,wall_s,cpu_s,peak_kb,exact) values(strftime('%s','now'),'$(hostname)','myrepo','$SWARM_NAME','repo','just build','just build',$wall,$cpu,$peak_kb,1)"
```

Read it with `swarm cost "<command>"` and `swarm cost --top [--repo R | --all-repos]`.
