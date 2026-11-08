# sw-lifecycle: who ends agents, cleans up after them, and spawns new ones

Written 2026-11-07 from this repo's sr-* swarm and jk_ledger's live 12-agent
swarm (`swarm.db` read with `mode=ro`), `hc ls`, `gh pr list`, the swarm code
and `swarm/research/`. It builds on [sw-locks.md](sw-locks.md): its worktree
snapshot (§4.1, §4.3) is also the "can this agent end?" signal.

## 1. What happened

**sr-* (PR repo, the communicator merges):**

- sr-a and sr-b finished at +14 and +16 min and went idle. Their last PRs (#7–#9) merged at
  +18 to +19 min. Nothing told them. Their tabs, worktrees and local branches
  stayed until sr-comms ran `swarm leave` for both at +23 min and removed the
  rest by hand. `origin/sr-c/locks` is still on the remote after PR #10 merged.
- sr-b dropped #4 meaning "release", which deleted it. `task release` fixed
  that.
- #6 (review sr-a's SKILL.md) couldn't say "after #3". sr-b learned #3 was
  ready only from sr-comms.

**jk_ledger (agents push to main), 31 min in:**

| Measure | Value |
|---|---|
| Agents | 13 (12 + jl-comms), all live, none ended |
| Tasks | 2 done, 15 claimed, 13 open, 5 dropped |
| Idle agents holding a claim | 11 of 13: waiting on the user's sign-off, on a missing export, or on memory |
| Digests "N open tasks and you are idle" | 5, to jl-comms (which takes no tasks) and to jl-2, jl-3 and jl-10, which held claims |
| Memory | At +30 min Claude Code killed jl-4, jl-5, jl-6, jl-7 and jl-9's builds and the shared dev db for low memory |

So:

1. **Idle is not finished.** Most idle agents are waiting with unlanded work.
   Ending them, or handing their claim to someone else, loses the work.
2. **Finished is "landed".** "Task done" means the PR exists or the commit is
   pushed. In a PR repo, review can still send it back. An agent is finished
   when its work is on main.
3. **Nobody watches for that moment**, so cleanup falls to the communicator,
   whose attention is the bottleneck the swarm exists to avoid.
4. **Every idle agent holds about 300 MB** (sw-substrate), and memory is what
   ran out in jk_ledger. Leaked agents aren't free.
5. **Big contexts make reuse expensive.** Each turn of a 150k agent resends
   150k tokens (cached), and the cold guard exists because waking one costs
   the whole context.

## 2. Options

**Who ends an agent**

| Option | Precision | Cost | Failure modes |
|---|---|---|---|
| E1. Today: persist; the communicator ends by hand | the communicator judges | its attention and a wake per check; leaks tabs, worktrees and branches | Doesn't scale past a handful; jk_ledger would need 13 checks |
| E2. Agent ends itself at `task done` | wrong: done ≠ landed | none | Gone before review asks for changes; ending itself means killing its own process mid-turn |
| E3. Agent ends itself when told its work landed | right | a wake per agent to say so, a full-context turn at 100–180k | Pays the cold-wake cost the swarm guards against, only to say goodbye |
| E4. watchd ends an agent once it is idle, has no claim, holds no lock and its work has landed | right, mechanical | a few git calls per idle agent per tick; no model | Needs a sound "landed" test (§4.2); ends an agent the human is about to talk to |

**Who cleans worktrees and branches**

| Option | Failure modes |
|---|---|
| C1. Communicator by hand (today) | As E1 |
| C2. The agent, before it ends | Only works if it learns of the landing (E3's wake) |
| C3. watchd, right after E4 ends the agent | Must never lose work: `git worktree remove` without `--force` refuses a dirty tree; delete a branch only when the landed test passed |

**Who takes the next task**

| Option | Cost per task | Quality | Failure modes |
|---|---|---|---|
| N1. A finished agent continues (persistent workers) | carries its whole context on every turn | knows the area; drifts (Cursor: "periodic fresh starts are still needed against drift") | Context grows to a relaunch anyway |
| N2. A fresh agent per task (Gas Town's polecats, the C compiler's `while true` relaunch, Cursor's fresh cycles) | startup: ~31k shared prefix plus the brief and orientation | fresh context; fits "reviewers get a fresh context" | Startup reading; more tabs churn |
| N3. Continue if the agent's context is small, else fresh | the cheaper of the two | as N1 or N2 | Needs a threshold |

**Who spawns when nobody is free**

| Option | Failure modes |
|---|---|
| S1. The communicator, on watchd's digest (today) | Each digest wakes it; jk_ledger's went to it 2 of 5 times |
| S2. watchd, within a cap the human sets | Spawns spend money: needs a cap; can overload the machine (jk_ledger's OOM) |
| S3. Never: a fixed roster | Open tasks starve when the roster is waiting on the human |

## 3. Recommendation

**E4 + C3 + N3 + S2**: the daemon does lifecycle; models only do work.
"Crons watch, models act" (Wheelhouse), applied to the swarm's own members.

- An agent never ends itself and never needs a wake to be ended. watchd ends
  it once it is idle, owns nothing and its work has landed. Then it removes
  the worktree and the branch, refusing anything dirty or unlanded.
- After `task done`, the agent takes the next task itself only if its context
  is under `SMALL_CTX` (40k, already the "cheap to wake" line). That is where
  carrying context costs no more than a fresh start. Otherwise it goes idle
  and is ended when its work lands, and a fresh agent takes new work.
  `swarm task done` prints which, so the brief needs no arithmetic.
- watchd spawns one fresh agent per open, unblocked, unclaimed task when no
  reusable agent is idle. It stays within `--max-agents`, which defaults to
  the live count when watchd starts (the size the human launched) and which
  the communicator raises with the human. It also needs free memory (§4.5).
- Task dependencies (`--after`) keep blocked tasks out of the pool, so the
  digest and spawn see only work that can start.
- Leases stop reopening a live agent's claim. Idle-with-claim is the common
  state (11 of 13 in jk_ledger), not abandonment. A live agent past its lease
  gets reported to the communicator; only dead or ended agents' claims reopen.

## 4. Spec

### 4.1 States

An agent is in exactly one of:

| State | Test | Lifecycle action |
|---|---|---|
| working | `status='working'` or hc says working | none |
| blocked | hc says blocked | tell the communicator (today) |
| waiting | idle, and owns a claimed task, a lock or unlanded work | none; persists |
| reusable | idle, no claim, nothing unlanded, `ctx_tokens < SMALL_CTX` | gets the digest |
| finished | idle, no claim, no lock, nothing unlanded, `ctx_tokens ≥ SMALL_CTX`, or no open task it could take | watchd ends it |
| ended | `agent.ended` set | release, cleanup |

The communicator (`SWARM_COMMS`) is exempt: never digested, never ended.

### 4.2 The landed test

`landed(agent)` uses `agent.wt` (sw-locks §4.1; null means no worktree means
nothing unlanded). After `git fetch -q origin main` once per tick (skipped if
the repo has no origin, using local `main`), let `B = origin/main`:

1. The worktree is clean: `git -C W status --porcelain` lists nothing (ignored
   files don't count).
2. And either `git merge-base --is-ancestor HEAD B` (push or merge commit),
   or for every path in `git diff --name-only $(git merge-base B HEAD) HEAD`,
   `git diff --quiet HEAD B -- <paths>` (squash and rebase merges land the
   same content under new commits).
3. If 2 fails but `gh pr list --head <branch> --state merged --json number`
   lists a PR, it landed and main has moved on over those files since.

The main checkout as `wt` is never landed-tested or removed. An agent with
`wt` = main checkout counts as having nothing unlanded only if (1) holds
there.

### 4.3 Ending (watchd tick)

For each agent in state *finished* (§4.1), skipping any whose hc status isn't
idle or done:

1. `release(c, name)`, set `ended`, `status='ended'`, log `end` with the
   reason (`landed`).
2. `hc kill <addr> && hc rm <addr>`.
3. Cleanup, if `wt` isn't the main checkout:
   - `git worktree remove <wt>`, no `--force`;
   - `git branch -D <branch>` (the landed test already proved its content is
     on main; `-d` refuses squash-merged branches);
   - `git push origin --delete <branch>` if `git ls-remote --heads origin
     <branch>` lists it.
   Any step that fails stops the cleanup. Post one `notice` to the
   communicator: "jl-6 ended; .worktrees/jl-6 not removed: <git's error>."
4. No other message. `swarm watch` shows the `end` event.

### 4.4 Taking the next task

`cmd_task done` appends one line after `done #N`, using the agent's
`ctx_tokens` from its last Stop:

- under `SMALL_CTX` and an open unblocked task exists: `context ~Nk: take the
  next task (swarm board).`
- otherwise: `context ~Nk: go idle. watchd ends you once your work lands; a
  fresh agent takes new work.`

The brief's **Ending** bullet becomes: "After `task done`, do what it prints.
Don't close your tab, end yourself or remove your worktree: watchd does that
once your work lands. If review asks for changes, you're still here to make
them."

### 4.5 Spawning (watchd tick)

Let `pool` be the open tasks whose `after` dependency is `done` (or have
none). For each task in `pool`, oldest first, while the conditions hold:

- no *reusable* agent exists (they get the digest instead, once per 15 min as
  today);
- live agents, excluding the communicator and ended ones, `< --max-agents`;
- `MemAvailable` in `/proc/meminfo` ≥ `--min-free-mem` (default 4 GiB). This
  is a knob, not a derived number. jk_ledger's builds were OOM-killed with 13
  agents on 31 GiB.

then:

- name = `<prefix><n>`: the prefix is the communicator's name minus `comms`
  (`jl-comms` → `jl-`), and n = 1 + the highest number used;
- claim the task for the new name first (`owner`, lease), so the next tick
  can't spawn for it again;
- `swarm spawn <name> --model <task.model or --model> -- "Board task #<id>:
  <title>. It is claimed for you; read its body with swarm board."`;
- log `spawn` with `data=auto #<id>`.

At most one spawn per task. A spawn that fails (launch.sh error) releases the
claim and posts a notice to the communicator.

`--model` defaults to the most common `agent.model` among non-communicator
agents. `--max-agents` defaults to the live non-communicator count when
watchd starts, so watchd refills the roster the human launched but doesn't
grow it. The SKILL tells the communicator to raise it only with the user.

### 4.6 Dependencies

- `task.after int` (nullable), `task.model text` (nullable).
- `swarm task add "<title>" [--after N] [--model M]`.
- `claim` of a task whose `after` task isn't `done` fails: "#6 waits on #3
  (claimed by sr-a)."
- `swarm board` shows `after #N` on such tasks; the open count in digests
  and the spawn pool exclude them.

### 4.7 Leases

`reap` changes:

- An expired claim reopens only if its owner is ended or dead (as found by
  the hc liveness check).
- For a live owner: one `notice` per task per lease period to the
  communicator: "jl-4 has held #5 for 2 h (idle 40 min)." The claim stays.
  `task renew` still exists for agents mid-work.

### 4.8 Digests

`watchd_tick`'s digest goes only to *reusable* agents (§4.1): idle, no claim,
under `SMALL_CTX`, not the communicator. Waiting agents and the communicator
never get it.

### 4.9 Tests (test_swarm.py, temp repos, stub `hc`)

- An idle, claimless agent whose branch is an ancestor of main gets `end`;
  its worktree and branch are gone.
- Same, but its branch was squash-merged (same content, other commits): ended.
- A dirty worktree, or a branch not on main: not ended.
- Idle with a claim: not ended, not digested, claim survives an expired lease.
- `task done` with `ctx_tokens=20000` and an open task prints "take the next
  task"; with 120000, "go idle".
- An open task, no reusable agent, under the cap: one spawn, task claimed for
  it. A second tick: no second spawn. At the cap: none.
- `claim` of a task with an unmet `--after`: refused.
- The communicator: never digested, never ended.

## 5. Interactions

- **sw-locks** supplies `agent.wt`, the per-tick snapshot and the "files"
  set. Lifecycle should be implemented after it, or carry §4.1 of that spec
  itself. Lock release on landing (sw-locks §4.4) and ending on landing
  (§4.3 here) are the same event.
- **relaunch** still covers an agent whose context runs high mid-task. A
  successor inherits the claim and `wt`. Its predecessor's `end` comes from
  relaunch (the successor kills it), not from watchd.
- **Cold guard** is unchanged. This design removes the main reason to wake a
  big idle agent: telling it its work landed.

## 6. Not covered

- **The human in an agent's tab.** watchd ends an agent the human may be
  about to type to. hc reports no "human attached" signal. If that happens,
  add a `swarm pin <name>` that exempts an agent.
- **Review after landing**: a post-merge bug in a finished agent's work gets
  a fresh agent from a new task. That is cheaper than keeping its author
  alive.
- **Fresh-agent startup cost** wasn't measured. The ~31k shared prefix is
  from sw-probe; orientation reading is per repo.
- **How many agents a Max plan sustains** remains unverified (sw-substrate).
  `--max-agents` is the guard.
- **Whether `hc kill` loses anything** (an unflushed transcript line) wasn't
  tested. relaunch already ends predecessors this way.
