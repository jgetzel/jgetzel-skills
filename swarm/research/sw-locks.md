# sw-locks: what should replace touch notices and leased locks

Measured 2026-11-07 against jk_ledger's live 12-agent swarm (read-only: its
`swarm.db` opened `mode=ro`; its worktrees read through a `--shared` bare clone
in a scratch dir). git 2.56, 12 cores. Prior-art notes came from a research
subagent; sources are at the end. `sw-locks-probe.py` reproduces the numbers:
`python3 -I swarm/research/sw-locks-probe.py ~/workspace/jk_ledger <scratch>`.

## 1. What went wrong in jk_ledger

| Measure | Value |
|---|---|
| Touch events | 310, of which **303 came from `bash_diff`'s `git status` diff**, 7 from edit tools |
| Overlap events / system messages | 681 / 670, to 13 agents in 20 minutes |
| Paths "touched" by ≥10 agents | 13 (`Main.hs` 12, `0069_measurement_targets.sql` 11, `Ledger.hs` 10…) |
| Where those files really differ from main | `0069_*.sql` in 1 worktree, `Main.hs` in 1, `Ledger.hs` in 8 |

Three separate faults:

1. **Misattribution.** Agents started in the one main checkout. `bash_diff`
   credits an agent with every path whose `git status` entry changed since
   its last Bash call, so each agent was "touching" everyone else's edits.
   jl-8 wrote `0069_*.sql`; ten other agents' Bash calls then reported touching
   it. The hook can't tell whose edit a dirty file is.
2. **Co-touch is not conflict.** Even with correct attribution, file overlap
   is mostly harmless (§5): 53 agent pairs shared a file, and one pair had a
   conflict that needed a person.
3. **The real hazard went unnamed.** The thing worth one loud message was
   "four agents have uncommitted edits mixed in one checkout". jl-1 and
   jl-comms found it by reading the noise, not because the tool said it.

Locks: the only use was reserving migration numbers (`migrations/0069` …
`0073`). `lock_holder` matches with `fnmatch`, and
`fnmatch("migrations/0070_warmup_rir.sql", "migrations/0070")` is false, so
**those locks guarded nothing**. They worked only as a visible reservation.
That is a real need git can't see: `0070_a.sql` and `0070_b.sql` merge cleanly
and still collide.

## 2. Options

Signal is measured on the probe run (§5): 16 worktrees, 53 pairs sharing a file.

| Option | Pairs flagged | Hook cost per call | At 50 agents | Failure modes |
|---|---|---|---|---|
| A. Today (PR #4): co-touch via edits + `git status` diff, ≤1 notice per agent, path and hour | most of the swarm, per path | `git status` on every Bash call (5–12 ms) | N notices per hotspot per hour; still misattributes in shared trees | Wrong attribution; arbitrary window; noise trains agents to ignore notices |
| B. Working sets: each worktree's diff vs its merge-base, file overlap | 53 | 10–25 ms if run in hooks, 0 in a daemon | O(N²) pairs on hotspots | Correct but low precision: registries make everyone overlap |
| C. B + `git merge-tree` trial merge, git's line-level conflicts | 27 (40 pair-files) | 0 in a daemon; 0.2–0.9 s per hotspot edit if run in hooks | merges only for overlapping pairs | Two appends to one export list "conflict"; that was 30 of 35 hunks in the first sample |
| D. C + token-level re-merge of each conflict hunk | **1** | 0 in a daemon | as C, plus ms per hunk | Misses semantic conflicts with no textual overlap (same as B and C); a misclassified hunk still surfaces at rebase |
| E. Ownership (CODEOWNERS-like, a file belongs to a task) | n/a | low | serializes hotspots: `Ledger.hs` is in 8 of 16 working sets | CODEOWNERS and OWNERS gate review; none handles hotspot files. Cursor's lock design ran 20 agents at 2–3 agents' throughput |
| F. Pessimistic per-file locks for all edits | n/a | low | contention on every hotspot | Cursor's failure; DPBench deadlock when acting simultaneously |
| G. Structured merge (Mergiraf) as classifier | likely ≈ D | an extra binary | as C | It merges unordered insertions (imports, members) but conflicts on ordered lists; it publishes no evaluation of its own, and third-party numbers warn it sometimes resolves conflicts silently |
| H. Repo-side: one entry per line or one file per entry for registries | removes the cause | none | best | Repo work, not the skill's. GitLab's changelog fragments, towncrier, Bazel `glob()` |

Locks (separate axis):

| Option | Covers | Failure modes |
|---|---|---|
| L1. Today: leased (2 h) glob locks, deny edit tools | anything, if matched | Prefix patterns silently match nothing; overlapping locks not refused; Bash violations misattributed like touches |
| L2. Reservations only: locks for what git can't see (number allocation, a schema both sides read), matched as glob or directory prefix, released when the work lands | the jk_ledger use | A forgotten lock blocks until landing or reap; deny tells the blocked agent to ask the holder |
| L3. Advisory leases (mcp_agent_mail: exclusive by default, 3600 s TTL, conflicts reported with the grant, optional pre-commit guard) | as L2 | Still path-based, so registries false-share; Gray & Cheriton call this "false sharing" and give write-shared files a lease term of 0 |

## 3. Recommendation

**D for overlap, L2 for locks, H as advice to repos**, with the conflict check
in `watchd` rather than in hooks:

- Attribute work by worktree, never by `git status` diffs. A worktree's diff
  against its merge-base is the ground truth and costs nothing to keep.
- Run trial merges in the daemon. Hooks get cheaper than today. The latency
  is one tick (30 s), and conflicts develop over minutes.
- Notify only on a hunk where both sides change the same tokens. In jk_ledger,
  that is 1 pair of 53 overlapping pairs. Notify once per conflict episode,
  not per time window. That replaces the one-hour rule with a state change:
  an episode starts when the conflict appears and ends when it is gone.
- Say once, loudly, when two agents share a worktree.
- The notice carries a fixed tiebreak ("whoever lands first wins; the other
  rebases"), so nobody negotiates. DPBench: "determined by the protocol, not
  by the model's capability"; a fixed ordering cut deadlock to 0%.

## 4. Spec

### 4.1 Which worktree is an agent's

- `agent.wt`: the toplevel (`repo_rel`'s first element) of the agent's latest
  edit-tool path, set in `pre-tool`. Bash cwd is **not** used: it says where
  a command ran, not which tree the agent edits (`git -C`, absolute paths).
  jk_ledger's 13 agents all started in the main checkout.
- Fallback when `wt` is null: the worktree whose branch is `<name>/…`
  (`git worktree list --porcelain`). Both swarms so far name branches that way.
- An agent with neither is outside conflict checks. `swarm who` shows `wt: ?`.

### 4.2 Shared trees (pre-tool, edit tools)

After setting `agent.wt = T`: if another live agent has `wt = T`, and no
`shared-tree` event exists for (this agent, T), log one and add context to
this agent, plus a `notice` to the other agent:

> `<T>` is also <other>'s worktree (<task>). Two agents' uncommitted edits in
> one tree mix and can't be told apart. Make your own: `git worktree add …`.

Once per (agent, tree) for the swarm's life. It never denies; a repo that
wants a hard rule can `swarm lock` a tree.

### 4.3 The conflict tick (watchd, every tick)

For each live agent with a worktree, in a single process:

1. **Snapshot.** Copy the worktree's index (`git -C W rev-parse --git-path
   index`) to a temp file. Then `GIT_INDEX_FILE=tmp git -C W add -A` and
   `write-tree`, and `commit-tree <tree> -p HEAD`, with `GIT_OPTIONAL_LOCKS=0`.
   This reads W only. Objects go to the shared store, unreferenced, and are
   pruned by gc after `gc.pruneExpire`. Use no refs. Seeding from the real
   index keeps the stat cache: 30 ms instead of seconds. Copying is safe
   because git replaces the index by rename. Store `{head, tree, commit,
   files}` in `agent.snap` (the column `bash_diff` used); `files` is
   `git diff --name-only <merge-base main> <commit>`.
2. **Candidates.** Pairs (a, b) with different `wt`, intersecting `files`, and
   a `(tree_a, tree_b)` key that differs from the last checked key for that
   pair. Unchanged pairs keep their verdict.
3. **Trial merge.** Run `git -c merge.conflictStyle=diff3
   --attr-source=<main> merge-tree --write-tree --name-only --no-messages
   <commit_a> <commit_b>`. Pin `--attr-source`: merge drivers otherwise come
   from the `.gitattributes` where watchd runs, and an untracked one changed a
   result in the subagent's test. Batch with `--stdin` if a tick runs long.
   Exit 0: clean. Exit 1: conflict. Anything else: log `conflict-error` and
   skip.
4. **Classify** each conflicted file. Read it from the result tree and split
   it into diff3 hunks (ours, base, theirs). Tokenize with `\w+|[^\w\s]|\n`.
   Get each side's changed base spans from `difflib.SequenceMatcher(base,
   side).get_opcodes()` (non-`equal` ops; an insert is the empty span
   `(i, i)`). The hunk is **real** if a span from ours and a span from theirs
   clash: both non-empty and overlapping, or one an insertion strictly inside
   the other's non-empty span. Two insertions at one point never clash. Code:
   `real_hunk` in `sw-locks-probe.py`, with asserts.
5. **Episodes.** Table `conflict(a, b, path, since, primary key(a,b,path))`
   with `a < b`. A real (a, b, path) not in the table starts an episode:
   insert it and queue a notice for both agents. A row whose pair was
   checked this tick without a real hunk on that path ends: delete it,
   silently. Rows for ended agents go in `release()`. Line-only conflicts
   log `conflict-compat` events for the retro and send nothing.
6. **Send.** At most one `notice` per agent per tick, listing every new
   episode (kind `notice`: never wakes, delivered at the next tool call):

   > Your uncommitted work conflicts with jl-9's (task #17: DEXA scans) in
   > server/src/Ledger.hs (your lines 120–131, theirs 118–140). Whoever lands
   > first wins; the other rebases onto it. Message jl-9 only if the two
   > changes can't both stand.

   Line ranges: find each side's hunk text in its own snapshot's file.
7. **Bash lock violations** come from the same snapshot. A path in `files` of
   an agent whose `wt` is not shared that matches another agent's lock gets
   one `system` message to both, once per (agent, path). This replaces
   `bash_diff`'s check, which shared trees misattributed.

### 4.4 Locks

- **Match**: a path is covered by lock `p` if `fnmatch(path, p)` or
  `path.startswith(p.rstrip("/") + "/")`. Bare prefixes like
  `migrations/0070` are not supported: write `migrations/0070*`. The brief
  says so.
- **Refuse overlap** in `cmd_lock`: refuse if either pattern matches the
  other, or either is a directory prefix of the other. The other agent's lock
  holds. This is approximate for two globs (`a/*.hs` vs `a/X*`); it errs
  toward allowing.
- **Lifetime**: released by `swarm unlock`, by `release()` when the agent
  ends, or by the tick when the holder's `files` once matched the lock and no
  longer do (the work landed or was reverted). Record `lock.seen=1` the first
  time it matches. The 2 h lease stays as a backstop for a live holder that
  is stuck; reap tells the holder, as today.
- Locks never block-wait. A denial says who holds the lock, and the brief's
  rule stands: message the holder. With no waiting there is no
  hold-and-wait, so no deadlock.

### 4.5 Removed

`touched()`, `told()`, `TOUCH_WIN`, the `touch`-table writes, and the porcelain
part of `bash_diff` (keep its `git push` logging). `swarm board`/`who` show each
agent's `files` from `agent.snap` instead of touches. `porcelain()` goes. The
`touch` table can stay in old dbs.

### 4.6 Tests (test_swarm.py, temp repos)

- Two worktrees append different names to one one-line export list: line
  conflict, no notice, one `conflict-compat` event.
- Both edit the same token: one notice to each; a second tick sends nothing;
  revert one side, tick (row gone), re-edit, tick: a new notice.
- Two agents edit in one worktree: one `shared-tree` notice each, not
  repeated.
- `swarm lock 'migrations/0070*'` denies an edit to
  `migrations/0070_x.sql`; `lock migrations/` then `lock migrations/a.sql` by
  another agent is refused; the lock goes once the holder's file lands.
- Cold-agent safety: tick notices are `kind='notice'` (no wake).

## 5. Prototype check

`sw-locks-probe.py` runs §4.3 steps 1–4 over every jk_ledger worktree.

| | Run 1 (13 worktrees) | Probe run (16 worktrees) |
|---|---|---|
| Pairs sharing a file / (pair, file) | 44 / 99 | 53 / 118 |
| git line conflicts: pairs / (pair, file) / hunks | 21 / 30 / 35 | 27 / 40 / 45 |
| Token-level real: pairs | 1 | 1 |

The one real pair is the main checkout against jl-3 on `Mcp.hs`: residue of
the shared-checkout phase, the case §4.2 names.

What the line conflicts were (run 1, 35 hunks): 27 were one-line Haskell
`module … (…)` export or `import … (…)` lists where both sides added names;
3 were the one-line `tools e = map ($ e) [...]` registry; 1 was two inserts at
one point; 4 were body code. Of the body-code hunks, `Importers.hs` was one
side restructuring `readExport` into guards while the other edited a string
literal in it, and `In.hs` was one side inserting a new type under a doc
comment the other side rewrote. Both are token-compatible and quick to fix
at rebase; neither needs the agents to talk.

Timing (median of 10; load average 31–42 on 12 cores while jk_ledger built,
then light):

| Step | Loaded | Light |
|---|---|---|
| Snapshot, index-seeded | 91 ms | 30 ms |
| Snapshot, empty temp index | — | 0.1–0.8 s per worktree; 76 s on the main checkout without its `info/exclude` |
| `merge-tree` per pair | 22 ms | 7 ms |
| `git status` (today's per-Bash hook cost) | 12 ms | 5 ms |
| Full tick, 16 worktrees, 53 pairs | 5.7 s | — |

At 50 agents a loaded tick is ~10 s of snapshots plus merges for overlapping
pairs whose trees changed. That fits in a 30 s tick on one core. If not:
`--stdin` batching (one process for all merges) and a small thread pool for
snapshots. The worst case is the first tick with everyone on one hotspot:
1,225 merges at 22 ms is 27 s, once.

## 6. Against the communicator's candidate

Read after §1–§5 were drafted. The candidate: working sets from the diff
against the merge-base, recomputed after each edit or Bash call; overlap
episodes; a merge-tree on episode start or content change; clean merges
silent apart from a one-line note before the first edit; conflicts get one
message with hunks; locks last until released or until the path leaves the
holder's working set.

Agree, and adopted: working sets as ground truth; episodes instead of
windows; trial merges on snapshots; silence on clean merges; locks released
when the work lands (§4.4, which this spec took from the candidate).

Reject, and why:

1. **Recompute in hooks.** Every edit to a hotspot would snapshot both sides
   and merge per overlapping peer. With `Ledger.hs` in 8 working sets, that
   is ~7 × (90 + 22) ms ≈ 0.8 s added to each such edit under load, while
   today's hook spends ~12 ms on `git status`. watchd does the same work with
   no hook cost, at most 30 s later.
2. **Line-level conflicts message.** Git's conflicts would have sent 27 pairs
   messages, 26 of them for compatible appends to one-line lists. The token
   re-merge brings it to 1.
3. **The pre-edit note on clean overlaps** is the co-touch notice again: 118
   (pair, file) overlaps in the probe run, all clean or compatible but one.
   `swarm who` already shows working sets for anyone who wants to look.
4. **No owner for a worktree.** The candidate doesn't say how an agent maps
   to its worktree. In jk_ledger, all 13 agents started in the main
   checkout, and four edited there. Two agents in one tree have identical working sets and a clean
   self-merge, so the candidate is silent on the run's one real hazard. §4.1
   and §4.2 cover it.
5. **No lease at all.** That frees a lock only on landing or death. A live
   holder stuck on a prompt keeps it. The lease stays as a backstop.

Where the candidate is better: notices land at the next tool call instead of
up to a tick later, and it needs no daemon. If watchd is down, this design
detects nothing; SKILL.md already makes watchd required.

## 7. Not covered

- **Semantic conflicts with no textual overlap**: two migrations numbered
  0070, a rename against a new caller, two functions with one name. Trial
  merges miss them by construction. Locks (reservations) and CI on the
  rebased result catch them. Crystal measured 1% build and 6% test failures
  among textually clean merges.
- **Conflict with main** (an agent's work against landed commits) is one
  cheap merge per agent per tick. It is left out because repo rules already
  rebase before landing; add it if the retro shows late rebases hurting.
- **Flapping**: a mid-edit snapshot can start and end an episode in
  consecutive ticks. Not seen. If the retro shows it, require two ticks.
- Renames and file/directory conflicts in `merge-tree` (exit 1 with no diff3
  hunks) count as real. Untested here.
- Repo advice for jk_ledger (option H): one export per line in `Ledger.hs`'s
  and `Mcp.hs`'s lists and the `tools` registry would make most of these line
  conflicts clean merges in git itself. Separate inserts merge; same-point
  inserts still conflict.

## Sources

- git merge-tree: https://git-scm.com/docs/git-merge-tree ; `--attr-source`: https://git-scm.com/docs/git#Documentation/git.txt---attr-sourcelttree-ishgt ; gitattributes `merge=union`: https://git-scm.com/docs/gitattributes
- GitHub on merge-ort (P50 7.7 ms, P99 330 ms): https://github.blog/engineering/infrastructure/scaling-merge-ort-across-github
- Cursor, Scaling long-running autonomous coding: https://cursor.com/blog/scaling-agents
- Anthropic, C compiler with parallel Claudes: https://www.anthropic.com/engineering/building-c-compiler
- DPBench (Hasan & BusiReddyGari): https://arxiv.org/abs/2602.13255
- mcp_agent_mail: https://github.com/Dicklesworthstone/mcp_agent_mail ; Gas Town: https://github.com/gastownhall/gastown
- Prior trial-merge tools: Clash https://github.com/clash-sh/clash ; moire https://github.com/jamescazzetta/moire
- Gray & Cheriton, Leases (SOSP 1989): https://courses.cs.duke.edu/spring15/cps210/readings/leases-sosp89.pdf
- Kung & Robinson, optimistic concurrency (1981): https://www.eecs.harvard.edu/~htk/publication/1981-tods-kung-robinson.pdf ; Agrawal, Carey & Livny via https://blog.acolyer.org/2016/01/07/concurrency-control-performance/
- Crystal (Brun et al., FSE 2011): https://homes.cs.washington.edu/~mernst/pubs/vc-conflicts-fse2011.pdf
- Agent PR conflicts (Xu et al.): https://arxiv.org/abs/2607.04697
- Mergiraf: https://mergiraf.org/languages.html , https://mergiraf.org/conflicts.html
- CODEOWNERS: https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/about-code-owners ; Chromium OWNERS: https://chromium.googlesource.com/chromium/src/+/HEAD/docs/code_reviews.md
- Registry patterns: https://about.gitlab.com/blog/2018/07/03/solving-gitlabs-changelog-conflict-crisis/ , https://towncrier.readthedocs.io/en/stable/ , https://bazel.build/reference/be/functions#glob
