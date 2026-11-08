# sw-ownership: atomic ownership in swarm

Audit and spec, 2026-11-08, against `swarm/swarm` at 4ee7a44 and this repo's
live `swarm.db` (read `mode=ro`). No code changes here; §6 is the build split.

## 1. Two incidents in the event log

**One task, two agents (#50).** 09:06:54 sr-comms adds #50 and #51. 09:07:03
it runs `swarm spawn sr-24 -- <#50 text>`; nothing is claimed. 09:07:05 watchd
logs both tasks `startable`; one `--interval` later (09:07:36) it auto-spawns
sr-25 for #50 and sr-26 for #51. sr-24 lands PR #51 (50b99e3, `Swarm-Agent:
sr-24`); sr-25 marks #50 done with "PR #51 merged (sr-24)". Two agents and
two startups for one change. SKILL.md says the interval exists "so an explicit
spawn that claims it first wins", but `cmd_spawn` never claims.

**The communicator reaped twice (events 1094-1099).** 08:44:54 and again
08:45:25, one watchd interval apart, "sr-comms is gone; its tasks and locks
are released", while its session was live; it was right again only after
`swarm join` at 08:59:21. The mechanism the code allows: `reap` ends any row
whose `hc` is not a live terminal. Revival didn't fix the binding: at the time `cmd_wait`
called `ensure_agent(c, n, status="idle")` without `hc`, which sets
`ended=null` and leaves the dead address. The next tick reaps it again. Every
reap releases the agent's claims and locks and wakes every peer with an
`@all` message.

## 2. Inventory of ownership facts

| Fact | Where | Writers (functions) | Readers that act on it |
|---|---|---|---|
| Task owner, state, lease | `task.owner/state/lease_until/question` | `cmd_task` claim, renew, done, block, unblock, release, drop; `release()`; `reap` (lease expiry); `lifecycle` (auto-claim and its rollback); `watchd_tick` (hc-blocked to `blocked` and back) | `pool`, `lifecycle` (end/reuse), `reap`, hooks' `task_of`, `cmd_run` (job's task) |
| Lock holder | `lock.path/agent/lease_until` | `cmd_lock`, `cmd_unlock`, `release()`, `reap` (expiry) | hook pre-tool `lock_holder` (deny-lock), `cmd_lock` overlap scan, `lifecycle` (end check) |
| Agent name to terminal | `agent.hc` | `ensure_agent` from `hook` (every event), `cmd_join`, `cmd_wait` (since #51), `cmd_spawn` (after launch) | `reap` (liveness), `end_agent` (`hc kill/rm`), `lifecycle` (idle check), `session_active`, `watchd_tick` (blocked) |
| Agent alive | `agent.ended` | set: `reap`, `cmd_leave`, `end_agent`. Cleared: `ensure_agent`, i.e. every hook event, join, wait, `task claim`, `lock` | `live_agents` (everything) |
| Waiter | `agent.waiter` | `cmd_wait`: newest pid wins | `cmd_wait` (superseded check), `cmd_post` (who wakes) |
| The communicator | `meta.comms`, plus any name ending `comms` (`is_comms`) | `cmd_watchd` (`insert or replace` at start) | `lifecycle` exemption and auto-spawn prefix, `task unblock` permission, `cmd_post` nudge, `comms_nudge` |
| The watchd process | nothing | (none) | (none) |
| Worktree attribution | `agent.wt`, else branch `<name>/…` (`wt_map`) | hook pre-tool on each edit: last edit wins | `conflict_tick`, `lifecycle` (landed check), `end_agent` (**removes the worktree and deletes the branch**), `sweep_worktrees` (exclusion), `cmd_who` |
| Job | `event` `job-start/job-end` (`agent`) | `cmd_run` | `live_jobs`, `remote_lines`, `clean_remote` |
| Read cursor | `cursor.last_msg_id` | `advance` (`max()` upsert) | `unread` |

Identity itself is just `$SWARM_NAME` (`me()`). Anything with the variable set
acts as that agent: a relaunched successor (launch.sh passes the environment
on, and `--settings` carries the name), a subagent, a shell.

## 3. Check-then-act and write-after-side-effect

The connection is `isolation_level=None`, so every statement autocommits.
There are no transactions anywhere in `swarm/swarm`. A multi-statement change
can interleave with another process and can stop halfway.

Check, then act in a separate statement:

1. **`cmd_lock`**: scans live overlapping locks, then `insert or replace` in a
   second statement. Two agents can both pass; on the same `path` the second
   silently replaces the first (the primary key is `path`).
2. **`cmd_task` renew, done, block, release**: owner/state checked on a row read
   at the top, then `update … where id=?`. If `reap` reopens the task and a
   peer claims it in between, the old owner's `done` marks the peer's task done.
3. **`cmd_task` unblock**: same shape (`state` check, unconditional update).
4. **`cmd_task` drop**: no check at all: any name drops any task, claimed or not.
5. **`cmd_task` claim** is the model to copy: `update … where id=? and
   state='open'` plus `rowcount`. Its `after` and context checks are separate
   reads, which is safe: a task never leaves `done`, and the context limit is
   advice.
6. **`reap` leases**: selects expired claims, then reopens `where id=?`. A
   `renew` in between is undone.
7. **`reap` locks**: selects expired locks, then `delete … where path=?`. A
   fresh lock on the same path made in between is deleted.
8. **`reap` agents**: `hc ls` snapshot, then `update agent set ended=? where
   name=?`. A rebinding in between (a successor's hook) is ended anyway.
9. **`lifecycle` end**: judges idle, no claim, no lock, landed (git and maybe
   `gh`: seconds), then `end_agent` releases and kills. If a message woke the agent and it
   claimed in that window, `release()` frees the new claim and `hc kill` ends it
   mid-work.
10. **`lifecycle` auto-spawn**: `pool()` snapshot, then a conditional claim
    whose `rowcount` is ignored. The spawn goes ahead even if a peer claimed
    the task in between.
11. **`lifecycle` names**: `max(n)+1` from the table. Two watchds (nothing stops
    a second one, e.g. across a communicator handoff) pick the same name, and
    both spawn for the same task.
12. **`ensure_agent`**: `insert or ignore`, revive, then one update per field;
    it runs on every hook event of every agent.
13. **`watchd_tick` blocked**: reads agent status, then flips the agent and
    "its first claimed task" unconditionally.
14. **`cmd_leave`, `release()`, `end_agent`**: ended mark and four releases as
    separate statements; a crash between them leaves a live claim on an ended
    agent (or the reverse).

Side effect first, intent after (or never):

15. **`cmd_spawn`**: launches the terminal, then writes the agent row. It
    checks no name: spawning a live agent's name rebinds that row to the new
    terminal. It never claims, so watchd's auto-spawn races it (incident 1).
16. **`end_agent`** writes first and kills after, which is the right order,
    but it removes `a.wt` without checking that no other live agent's `wt` or
    `cwd` is in it (`sweep_worktrees` checks; `end_agent` doesn't). An agent
    that once edited in a peer's tree is attributed to it (last edit wins).
17. **`cmd_watchd`** takes `meta.comms` by `insert or replace`: the newest
    watchd is the communicator, and the old one keeps ticking.

Already correct, and kept as they are: `cmd_unlock` (one `delete … and agent=me`), `advance`
(monotonic upsert), the `jobs` counter (atomic upsert `returning`), `cmd_run`
(logs `job-start` before it runs), the auto-claim before auto-spawn (intent
first, rolled back on launch failure).

## 4. The rule

1. **One ownership change, one `begin immediate` transaction.** The check and
   the write sit in the same transaction, or the write is one conditional
   statement (`… where id=? and owner=? and state='claimed'`) whose `rowcount`
   decides success. WAL readers aren't blocked; writers queue on
   `busy_timeout`. No subprocess (`git`, `gh`, `hc`) runs inside a
   transaction, so one is held for milliseconds. watchd re-checks inside the
   write what it judged outside it (a lease still expired, an `hc` still the
   one it saw dead, an agent still idle with no claim or lock).
2. **The bound terminal address is the fencing token.** `agent.hc` changes only
   in `swarm join`. Every other command and hook that writes as `$SWARM_NAME`
   passes if `$HC_TERMINAL_ID` equals the row's `hc` or the row is
   unbound (`hc` null, as right after a spawn or for a session outside Herdr).
   Otherwise it is refused with who holds the name: "sr-27 is bound to t11g;
   this terminal is t12a. `swarm join --takeover` moves it here." A hook from
   an unbound terminal writes nothing and adds that line once as context. It
   never denies the tool call, so a predecessor finishing its last turn isn't
   broken. `swarm join` binds a new or ended row, or one whose terminal `hc ls`
   doesn't show live. A live binding moves only with `--takeover`, which logs
   `takeover` with the old and new address. watchd's own writes are fenced the
   same way: `reap` ends `where name=? and hc=<the dead address>`.
3. **Intent before effect.** Write what you are about to do, then do it, then
   record the outcome or undo the intent. `swarm spawn <name> --task N`
   reserves the name (refused if a live agent has it) and claims #N in one
   transaction, then launches, then binds `hc` (`where hc is null`). If the
   launch fails it ends the row and reopens #N. Auto-spawn is the same call. A
   claimed task is never startable, so watchd's one-interval wait goes.
4. **Ended agents return only through `join`.** `ensure_agent` stops clearing
   `ended`. A hook or command from an ended agent writes nothing and says
   "sr-27 was ended at 08:44 (agent gone); `swarm join` to return."

## 5. What changes

**Relaunch and handoff.** Today a successor inherits `$SWARM_NAME`, and its
hooks and the predecessor's overwrite `hc` on every tool call until one
of them dies. If watchd ticks while the row names the killed predecessor,
the agent is reaped: claims and locks released, `@all` told it is gone,
possibly an auto-spawn for its task. Then the successor's next hook silently
revives it, without the claims. Under the rule the successor takes one explicit
step before anything else: **`swarm join --takeover`**, then it ends the
predecessor. From that moment the predecessor's hooks and waiter are fenced
out, its death is not the agent's death, and claims, locks and `wt` stay with
the name. The relaunch skill's first handoff item, swarm `brief.md` and swarm
`SKILL.md` (communicator handoff) each gain that line. The communicator, which
has no hooks, does the same; `cmd_watchd` takes over `meta.comms` and a
`meta.watchd` record (pid and terminal) the same way, so the old watchd sees
it no longer holds the record and exits.

**PR #51's wait rebinding.** #51 made `swarm wait` bind `$HC_TERMINAL_ID`
so a hookless communicator gets its terminal recorded. That is the bug class
of incident 2: two terminals with one name rebind each other from their
waiters. With fencing, `wait` binds only an unbound row. From a terminal that
isn't bound it exits 0 (no wake) with the holder line on stderr. The
communicator's binding comes from `join` / `join --takeover`, which SKILL.md
already makes its first step. #51's other effect, an unbound comms row getting an
address, is kept through the unbound case.

## 6. Decision 6 (information, not gates)

Decision 6 is about contention for shared capacity (memory, CPU, slots): tell
agents what is true and let them choose, never queue or ration. Ownership is a
different kind of question: a task, a lock or a name has exactly one holder, or the board
lies. Refusing a second writer is the same kind of check as the existing claim
`rowcount` and lock-overlap refusal, not rationing. The refusals are
information too: each names the holder and the way forward (message it, or
`--takeover`). Nothing waits on a slot or a timer. The rule removes one timer:
auto-spawn's full-interval wait, which stood in for the missing claim. Leases
keep their current meaning (decision 7 untouched).

## 7. Build tasks (proposed, not on the board)

Each lands as its own PR with `python3 -B swarm/test_swarm.py` passing.

1. **Transactions for every ownership write.** A `tx(c)` context manager
   (`begin immediate` / commit / rollback). `cmd_lock` refuses an overlapping
   or same-path live lock inside the transaction (no `insert or replace` over
   a peer). `cmd_task` renew/done/block/release/unblock become conditional
   updates on owner and state and check `rowcount`. `drop` of a claimed task is
   refused unless the caller is its owner or the communicator. `reap` re-checks what it judged
   (`lease_until<t`, the dead `hc`). `release()`, `cmd_leave` and the end paths each
   run in one transaction. *Done:* tests show a second `lock` on a held path is
   refused and the first holder kept, `done` after a reap and re-claim by a
   peer fails, `reap` doesn't reopen a lease renewed after its select, and a
   lock held open in a second connection makes `cmd_lock` wait, not double-write.
2. **Fencing by terminal (after 1).** `ensure_agent` splits: `bind` (join only)
   and a fenced `touch` that writes nothing for a mismatched or ended row. `join`
   refuses a live binding unless `--takeover` (logged `takeover`, old to new). Hooks
   no-op with one context line; commands refuse with the holder. `wait`
   binds only an unbound row and exits 0 when fenced (replaces #51's rebind).
   *Done:* tests: a hook or wait from another terminal doesn't change `hc`; a hook
   from an ended agent doesn't revive it; `join` on a live name is refused naming
   the holder; `--takeover` moves it and logs; `reap` doesn't end a row
   re-bound after its `hc ls`.
3. **Spawn writes intent first (after 1).** `swarm spawn <name> --task N`:
   reserve the name (refuse a live one) and claim #N in one transaction, launch, bind,
   or roll back on launch failure. `lifecycle` auto-spawn goes through it and
   skips a task whose claim lost the race. The startable-interval wait is
   removed. SKILL.md's spawn instructions use `--task`. *Done:* tests with a
   fake launch.sh: the task is claimed by the new name before launch runs; a
   failed launch reopens it and ends the row; an auto-spawn for a task a peer
   claimed between `pool()` and the claim spawns nothing; spawning a live
   name is refused.
4. **Handoff by takeover (after 2).** relaunch `SKILL.md` (first handoff item),
   swarm `brief.md` and `SKILL.md`: the successor runs `swarm join --takeover`
   before it ends the predecessor. *Done:* the three texts say so; a test
   binds a successor by takeover, removes the predecessor's terminal from the
   fake `hc ls`, and `reap` leaves the agent, its claim and its lock alone.
5. **Safe ends (after 1).** `lifecycle` ends an agent with one conditional
   transaction (still idle, no claim, no lock, same `hc`) before `hc kill`;
   `end_agent` doesn't remove a worktree that another live agent's `wt` or
   `cwd` is in (reuse `sweep_worktrees`' `used` check). *Done:* tests: an agent
   that claimed after the end decision is not ended; a worktree shared with a
   live peer is not removed.
6. **One watchd (after 2).** `cmd_watchd` takes `meta.watchd` (pid, terminal)
   and `meta.comms` in one transaction. It refuses while another live watchd
   holds them, unless `--takeover`. Each tick checks it still holds the record and
   exits if not. *Done:* tests: a second watchd is refused naming the first;
   after a takeover the old one's next tick exits without writing.

Not proposed: dropping the `*comms` name-suffix rule in `is_comms`. Task 6
makes `meta.comms` reliable, after which the suffix rule could go, but nothing has gone wrong with it yet.
