# sw-worktrees: one worktree per agent, or something else?

Measured 2026-11-07 on this machine (12 cores, 31 GB RAM, ext4 on NVMe,
git 2.56, jj 0.46, kernel 7.3) against scratch copies of jk_ledger. Its
checkout was only read: a `--shared` bare clone in the scratchpad was the
base for every tree. `sw-worktrees-probe.lua` reproduces the checkout timings:
`luajit swarm/research/sw-worktrees-probe.lua ~/workspace/jk_ledger <scratch>`.
The build timings are commands in §3. Prior-art facts came from a research
subagent reading primary docs and repos; the sources are at the end.

## 1. What went wrong in jk_ledger

From the retro log (12 agents, 31 tasks):

- **Agents edited the main checkout.** Four agents (jl-3, jl-6, jl-7, jl-8)
  edited it directly, with uncommitted hunks interleaved in 10 shared files.
  `orchestration.md` said to make a worktree. But agents are *spawned in* the
  main checkout, and the brief did not say it. jl-1 found the mix from
  touch-notice noise, not from any tool.
- **The OOM at 18:15.** About six GHC processes ran at 5.5 GB each. Three were
  orphans (16 GB), and two of those sat in the **main** checkout. Orphan
  cleanup could not have caught them: it spares any directory a live agent's
  `cwd` is in, and `swarm spawn` records every agent's `cwd` as the main
  checkout.
- **Cold caches.** "Fresh-worktree cabal build = full lib compile ~12 min/6.6
  GB", and many agents queued both that build and `nix build .#server`.
  13 builds sat queued behind two slots.
- **Disk.** Worktree build directories were small (<130 MB). The growth was
  the Nix store: one `nix build .#server` output per agent's tree.

So the hazard is not "worktrees are expensive". It is two things:

1. Agents start where they should not edit.
2. A new tree starts with no build cache, so every agent pays a full compile
   at the same time.

## 2. Options

Costs are per agent on jk_ledger: 381 tracked files, 3 MB pack, 5 MB
checkout. The time is the median of 5 runs.

| Option | Setup | Disk | What it shares | What breaks |
|---|---|---|---|---|
| **A. Shared main checkout** | 0 | 0 | everything | One index, HEAD, stash and branch. A peer's half edit breaks your build. `git add -A` takes peers' files. A rebase or stash moves files under everyone. Edits can't be attributed (sw-locks §1). Here the main checkout is also the user's live skills. |
| **B. `git worktree add`** | **29 ms** | 5.1 MB | object store, refs, config, hooks | Untracked files and build caches start empty. One branch per worktree. Submodule support is incomplete (git BUGS section). |
| B′. B + sparse cone (`server/` only) | 14 ms | 1.0 MB | as B | Saves nothing that matters at this size. Builds that read the whole tree break: the flake imports `web.nix` and `db.nix`. |
| **C. jj workspace** (colocated, 0.46) | 71 ms | 5.1 MB | as B: since jj 0.46, a non-default colocated workspace *is* a git worktree (`.git` file → `.git/worktrees/<ws>`, checked here) | Detached HEAD. There is no `<name>/…` branch for sw-locks' fallback. The repo must be jj-initialized. Concurrent ops are lock-free and "might conceivably lose some bookmark pointers" in colocated repos. |
| D. `git clone --shared` | 37 ms | 5.3 MB | objects, read-only through alternates | Git calls it "possibly dangerous": the source's gc can prune objects and "the cloned repository will become corrupt". New objects stay in the clone. Peers and watchd can't see them (§5). |
| D′. `clone --reference` | 80 ms | hard links + alternates | as D | as D |
| D″. `clone --no-local` | 338 ms | 8.4 MB | nothing | Full copy. Each clone has its own refs, so the swarm can't see branches without fetches. |
| E. CoW copy (`cp --reflink`) | n/a | — | file extents | **ext4 has no reflink**: `cp --reflink=always` fails "Operation not supported", and `auto` silently does a full copy. It needs btrfs or XFS (`reflink=1`). |
| E′. overlayfs upper per agent | ~3 ms per mount (rootless `unshare -rm`, `userxattr`) | upper only | lower layer | The lower layer must be a **frozen** copy: kernel docs call changes to it while mounted "undefined". The agent must be launched inside the mount namespace. Its commits live in its upper dir, invisible to watchd. Gc copies up whole packs. |
| F. Container or VM per agent (Codex cloud, Devin, Cursor, container-use, OpenHands) | seconds to minutes; image builds | image + tree | an image or snapshot; Nix store if mounted | Isolates the runtime too (ports, db), which is its real value. OpenHands bind-mounts the host repo read-write, so it isolates nothing on disk. Codex's Linux sandbox makes `.git` read-only, so committing needs escalation. Memory is not saved. |
| G. Patch queue (agents emit diffs, one integrator applies) | — | — | — | Each agent still needs a tree to build and test in, so it replaces landing, not isolation. The integrator serializes everyone, and the repo's PR/rebase flow is already a queue. Gas Town's "Refinery" is one; it still gives each worker a worktree. |

Build caches are a separate axis and apply to every option (§3).

**What other tools do.** Every parallel-agent tool checked defaults to a git
worktree per agent:

- Claude Code's `--worktree` and `isolation: "worktree"`, at
  `.claude/worktrees/<name>`, branch `worktree-<name>`;
- the Codex app, detached, in `$CODEX_HOME/worktrees`;
- Conductor, claude-squad, Uzi, Vibe Kanban, Gas Town and Sculptor;
- container-use, which keeps worktrees of a bare fork and runs a container
  over each.

Each solves the empty-tree problem the same way:

- **a per-repo setup script**: Conductor setup with `$CONDUCTOR_ROOT_PATH`,
  Uzi `devCommand`, Vibe Kanban, Sculptor, Cursor `install`, Devin
  `initialize`;
- **a list of ignored files to copy**: `.worktreeinclude` in Claude Code,
  Codex and Conductor; Claude Code also has `worktree.symlinkDirectories`.

Aider has no parallel mode: it works in, and auto-commits to, your checkout.

## 3. Cost per agent, and memory at N = 12

### Build caches: measured

Each row is jk_ledger at one commit (67f757e) in a fresh worktree.
`cabal build lib:jk-ledger` stops at `Ledger.hs`, which needs the dev db at
compile time (none was running), so the cabal rows cover 9 of 14 modules. The
time and peak RSS come from GNU `time -v`.

| Cache seed | cabal: modules compiled, wall, peak RSS | spago build: modules, wall, peak RSS |
|---|---|---|
| none (cold) | full compile; the retro measured ~12 min / 6.6 GB | 596, 31 s, 1.7 GB |
| `cp -r` of main's caches (stale: built 13:44 and 10-27) | 6 of 9, 11 min, 8.9 GB | — |
| `cp -a` of main's `output/`, `.spago` (stale) | — | 45, 20 s, 1.7 GB |
| **`cp -a` of a current cache from another worktree** | **0 of 9, 3.8 s, 0.43 GB** | **0, 0.7 s, 0.32 GB** |
| `cp -r` (no `-p`) of that same current cache | 4 of 9, 10 min, 8.8 GB | — |
| same tree, no copy (control) | 0 of 9, 1.1 s | — |

What the table shows:

- **A copied cache works at a new path.** cabal reports "configuration
  changed" and reconfigures in about 3 s, and GHC reuses every object. GHC
  checks a source hash in each `.hi` and needs `.o` mtime ≥ `.hi` mtime
  (GHC user guide), so **mtimes must survive the copy**. `cp -r` loses them:
  "Missing dynamic object file" and a 10-minute rebuild. Use `cp -a`.
  (jk_ledger's `orchestration.md` says `cp -r … web/output`.)
- **A seed is only as warm as its source.** The main checkout's caches were
  hours or days behind main, so seeding from them saved little for cabal
  and about a third for spago. The best seed is the newest tree built near
  `origin/main`.
- **Copying is cheap.** `cp -a` takes 104 ms for 172 MB of `dist-newstyle`
  and about 0.7 s for 88 MB of `web/output` (many small files).
  `cp -al` (hard links) takes 55 ms but is unsafe: a tool that writes in
  place changes every copy.
- **Sharing one cache directory is not an option.** cabal builds local
  packages "always … locally for the project" in `dist-newstyle`. The
  cross-project store (`~/.local/state/cabal/store`, 1.1 GB here) already
  holds dependencies and locks each unit, and every option shares it. Two
  agents building different sources in one `dist-newstyle` (option A, or a
  symlinked directory) overwrite each other's objects.
- **`nix build .#server`** is a sandboxed derivation: any source change
  rebuilds the whole package, whatever the tree. The store dedupes
  dependencies, and identical derivations block on each other instead of
  building twice. Its per-agent cost (disk growth, about 2 min of GHC) does
  not depend on the isolation choice. That is a repo question: use
  `cabal build` in the loop and run `nix build` once before landing.

### Per agent, jk_ledger

| | Shared main (A) | Worktree, cold (B) | Worktree + `cp -a` seed (B + seed) |
|---|---|---|---|
| Setup | 0 | 29 ms | 29 ms + ~0.8 s |
| Disk | 0 | 5 MB, then +130 MB `dist-newstyle` and +97 MB web after the first builds | 5 MB + 270 MB at once |
| First server build | none, if main is current; but it races peers' builds in one `dist-newstyle` | ~11–12 min, 6.6–8.9 GB | seconds, under 0.5 GB, plus the touched modules |
| First web build | as left | 31 s, 1.7 GB | 0.7 s, 0.3 GB |

### Memory at N = 12 on 31 GB

- **Claude Code**: about 0.4 GB RSS per session (390–430 MB measured), so
  12 × 0.4 ≈ **5 GB** in every option.
- **The tree itself**: nothing. Git and jj worktrees share the object store
  and the page cache.
- **Builds** decide it:
  - cold, 12 agents each need one 6.6–8.9 GB compile in the same first
    hour, and only **2–3 fit** beside the agents and the dev db. That is the
    18:15 OOM and the 13-deep queue.
  - seeded, a first build recompiles only what the agent touched. Its peak
    scales with those modules: 0.43 GB for a no-op. A `Ledger.hs` edit was
    not measured, because the module needs the dev db.
- **Sharing a checkout does not save build memory.** Agents in one tree
  still compile separately, on top of each other. The only lever is how
  much each build recompiles, and that is cache warmth.

**Every option, the same way.** Options B through E′ all start with empty
caches and all take the same seed. Their memory is the same, because they
share the kernel's page cache for objects and sources. F adds a container
runtime per agent (not measured). If each container keeps its own Nix or
cabal store, it loses the shared dependency store and recompiles
dependencies as well. A shares the caches and races on them (above).

**Result:** per-agent isolation costs ~30 ms and 5 MB. The cost people feel
is the cold cache, and a 1 s `cp -a` from a fresh seed removes it.

## 4. The cases for sharing the main checkout

The jk_ledger communicator proposed: worktrees for committing agents, read-only
agents share main, spawn sets the mode. Tested case by case:

| Case | Does sharing help? | What to do |
|---|---|---|
| Agents that never commit (reviewers, researchers) | Little. It saves 30 ms. In exchange the agent reads the user's possibly dirty, possibly stale main instead of `origin/main`. A reviewer needs the PR's branch, which main doesn't have. A researcher usually lands a file (this task did), so it commits after all. | Give them a worktree too, detached at `origin/main`. They can still read main by absolute path. |
| One committer with helpers on separate files | Yes, but the helpers are **Agent-tool subagents** of that committer. They run in its tree and its process, so swarm sees one agent. | Nothing new. Peer swarm agents on separate files land separately. |
| One shared runtime (dev server, db, file watcher) | The runtime is shared, not the tree. jk_ledger's `nix run .#dev` serves the main checkout and owns :8787 and `.dev`. Worktrees point at its socket (`TPG_SOCK=<main>/.dev/.s.PGSQL.5432`). | The repo's setup links or exports the runtime's address. A runtime that must serve the agent's own code (e2e against its change) needs a per-agent port; that is the repo's choice. |
| Cold build caches | Sharing one `dist-newstyle` breaks under concurrent builds (§3). | Seed caches with `cp -a` at spawn. |
| Non-code work (docs, board triage) | Docs commit, so no. Board work (`swarm` only) edits nothing. | A worktree; it costs nothing. |

In each case, either the agent gets the shared thing from its own tree (a
socket, a seed, an absolute read path), or the "sharing" is subagents inside
one swarm agent. **No case needs two swarm agents in one working tree.** A
per-agent mode would be a choice the spawner has to get right, and the
jk_ledger agents that edited main were exactly the ones nobody expected to
need a tree. So I reject the mode. I agree with the rest of the proposal:
spawn creates the tree, and the repo supplies the location, the setup and
which caches can be seeded.

## 5. How sw-locks and lifecycle depend on the choice

| Mechanism (built) | Worktree per agent (B/C) | Shared main (A) | Separate clones, overlay, containers (D/E′/F) |
|---|---|---|---|
| Attribution (`agent.wt` from edit paths, `<name>/…` branch fallback) | Exact once spawn records `agent.wt`. The fallback then isn't needed: jj's detached workspaces have no branch, and spawn's record covers them. | Everyone has the same `wt`, so attribution fails. The `shared-tree` notice fires, after the fact. | Paths fall outside `git worktree list`. `wt_map` finds nothing, so the agent is "outside conflict checks". |
| Trial merges (watchd snapshots → `merge-tree`) | Work. Snapshots go into the shared object store, and any pair merges. | Self-merge of one tree is always clean, so the run's one real conflict (main vs jl-3, `Mcp.hs`) is invisible by construction. | Each clone or upper dir writes objects watchd's repo can't read, so merges fail. That needs a fetch per agent per tick. |
| `landed()` / `end_agent` (remove the worktree and branch) | Work. Spawn-made trees are always non-main, so they get cleaned. | Never removes main (correct), and main's dirt blocks `landed()` for everyone in it. | Unknown paths are never cleaned up. |
| Orphan kill (cwd under an ended agent's tree and no live agent's) | Precise, **if `agent.cwd` is the agent's worktree**. Today `cmd_spawn` records the spawner's `os.getcwd()`, which is main for every agent. | Main is always "live", so orphans there are never killed. That was jk_ledger's 16 GB. | — |
| `swarm.db` at `<git common dir>/swarm/` | Shared: worktrees have one common dir. | Shared. | Clones get their own common dir. This works only because `SWARM_DB` is in each agent's settings. |

So trial merges, attribution, cleanup and orphan kill all assume
**worktrees of one repository, one per agent, with `agent.wt` and
`agent.cwd` set to that tree**. jj colocated workspaces qualify: they are git
worktrees. Clones, overlays and containers would each need a sync layer.

## 6. Recommendation

**One git worktree per swarm agent, created by `swarm spawn`, always; caches
seeded with `cp -a` by a repo-supplied list; no read-only mode.** Not
`claude --worktree`, for three reasons:

- its branch name (`worktree-<name>`) and its own cleanup sweep compete with
  watchd's `end_agent`;
- `symlinkDirectories` would share `dist-newstyle`, which §3 rules out;
- `.worktreeinclude` copying is undocumented on mtimes.

### What `swarm spawn` sets up

1. **The tree.** `git worktree add <dir>/<name> -b <name>/work origin/main`
   (or `main` when there is no remote).
   - `<dir>` defaults to `<main checkout>-swarm/`, a sibling, so nothing
     scanning the main tree sees it.
   - The branch keeps sw-locks' `<name>/…` convention.
   - If the name is taken (a relaunch successor), reuse the existing tree.
2. **The record.** `agent.wt` and `agent.cwd` are set to the tree, and
   `launch.sh` runs from it (it uses `--cwd "$PWD"`). The agent starts there,
   so editing main stops being the default. This also makes orphan kill and
   `end_agent` exact.
3. **The seed.** For each path in the repo's `seed` list, `cp -a` it from the
   **seed source** into the tree, skipping any path that is missing.
   - The seed source is the most recently landed agent's cache: before
     `end_agent` removes a landed worktree, it moves (`mv`, same filesystem,
     instant) the seed paths to `<git common dir>/swarm/seed/`. Until one
     exists, the source is the main checkout.
   - Log the source's age in the spawn event so the retro can see stale
     seeds.
4. **Setup.** If the repo has a `setup` command, run it in the tree with
   `SWARM_MAIN=<main checkout>`, with a timeout.
   - A failure goes into the agent's first message ("setup failed: …"). It
     doesn't abort the spawn: information, not a gate.
5. **Nothing else.** No deny rule on main (§7 says why).

### What the repo supplies

These go in `.claude/swarm.json`, beside the existing `heavy`. All of them
are optional:

```json
{
  "worktrees": "../jk_ledger-swarm",
  "seed": ["server/dist-newstyle", "web/output", "web/.spago"],
  "setup": "ln -s \"$SWARM_MAIN/.env\" .env"
}
```

- `seed`: gitignored build outputs that are safe to copy (path-independent,
  or rebuilt on a path change, as cabal reconfigures).
- `setup`: env files and runtime addresses (dev db socket, ports). jk_ledger
  would move its `TPG_SOCK=<main>/.dev/…` line here from `orchestration.md`.
- Repo rules (`orchestration.md`) keep only what the tree can't do for
  itself: "one dev stack, from main", landing, CI.

### What the brief says

Replace the first sentence of "Own worktree, conflict notices" with:

> You start in your own worktree (`$PWD`, branch `<name>/work`); work and
> commit only there. The main checkout belongs to the user: read it, never
> edit it.

Leave the rest of that bullet (conflict notices, locks) as it is. Add nothing
about creating worktrees: spawn has already done it.

## 7. Rejected, and why

- **A read-only mode that shares main.** §4: no case needs it. It adds a
  choice the spawner gets wrong, and it hides real conflicts from trial
  merges.
- **Denying edits outside the agent's tree** (Claude Code's worktree mode
  blocks main). This is a gate, and the user prefers information (the
  `shared-tree` notice already says it). With the agent starting in its own
  tree, the cause is gone. If the retro still shows main edits, revisit this.
- **Clones, overlayfs, reflinks.**
  - They save nothing over a 29 ms worktree.
  - Reflink is unavailable on ext4.
  - They break §5's mechanisms: separate object stores, and paths
    `git worktree list` doesn't know.
  - overlayfs also needs a frozen lower layer and a namespace launch per
    agent.
- **Containers per agent.** They are worth it for runtime isolation (a
  private db or port per agent), not for files. That is a repo-level setup
  choice, and it can live in `setup` (`podman run …`) later. It saves no
  memory.
- **Patch queues.** They don't remove the need for a tree to build in, and a
  single integrator serializes the swarm.
- **Sparse checkout by default.** Nothing to save at jk_ledger's size, and it
  breaks whole-tree builds. A huge monorepo could add a `sparse` key to
  `swarm.json` later.
- **jj.** It works and isn't needed. Its colocated workspaces are git
  worktrees, so a jj repo already fits this design if spawn records
  `agent.wt` rather than relying on branch names.

## 8. Not covered

- **The memory of a seeded build that touches a big module.** `Ledger.hs`
  needs a live dev db. Measure it in the next run's retro (the machine note
  already records heavy processes by agent).
- **How stale the landed-agent seed gets.** If main moves many commits
  between landings, the seed gets older; spago lost a third of its gain from
  a 10-day-old seed. If the retro shows it, a watchd tick could
  `cabal build` a seed tree at `origin/main` after each landing, in the
  background. Not proposed now: it is a heavy process nobody asked for.
- **Git gc with 12 committers and watchd snapshots** on one object store.
  Git documents a low risk of concurrent-gc corruption. A snapshot is needed
  for one tick, far less than `gc.pruneExpire` (2 weeks). Not seen in either
  run.
- **Submodules**: git warns against several checkouts of a superproject.
  Neither repo has submodules.
- **Windows and macOS**: untested; `cp -a` and siblings are POSIX.

## Sources

- git worktree: https://git-scm.com/docs/git-worktree ; sparse-checkout: https://git-scm.com/docs/git-sparse-checkout ; clone `--shared`/`--reference`: https://git-scm.com/docs/git-clone ; gc concurrency: https://git-scm.com/docs/git-gc
- Claude Code worktrees, `.worktreeinclude`, `worktree.symlinkDirectories`, `WorktreeCreate`: https://code.claude.com/docs/en/worktrees , https://code.claude.com/docs/en/hooks
- Codex sandbox: https://learn.chatgpt.com/docs/sandboxing , https://github.com/openai/codex/blob/main/codex-rs/linux-sandbox/README.md ; app worktrees: https://learn.chatgpt.com/docs/environments/git-worktrees ; cloud: https://developers.openai.com/codex/cloud/environments.md
- OpenHands: https://docs.openhands.dev/openhands/usage/sandboxes/docker , https://github.com/OpenHands/software-agent-sdk/issues/5307
- Aider: https://aider.chat/docs/git.html
- Devin: https://docs.devin.ai/onboard-devin/environment , https://docs.devin.ai/onboard-devin/environment-yaml ; Cursor: https://cursor.com/docs/cloud-agent/setup
- container-use: https://github.com/dagger/container-use
- jj: https://github.com/jj-vcs/jj/blob/main/docs/working-copy.md , https://github.com/jj-vcs/jj/blob/main/docs/technical/concurrency.md , https://github.com/jj-vcs/jj/blob/main/CHANGELOG.md (0.46 colocated workspaces)
- reflink: https://man7.org/linux/man-pages/man2/ioctl_ficlone.2.html , https://btrfs.readthedocs.io/en/latest/Reflink.html ; overlayfs: https://docs.kernel.org/filesystems/overlayfs.html
- cabal store vs dist-newstyle: https://cabal.readthedocs.io/en/stable/nix-local-build.html ; GHC recompilation: https://downloads.haskell.org/ghc/latest/docs/users_guide/separate_compilation.html ; spago paths: https://github.com/purescript/spago#file-system-paths-used-in-spago ; Nix multi-user: https://nix.dev/manual/nix/2.34/installation/multi-user
- pnpm store: https://pnpm.io/settings/store ; ccache sharing: https://ccache.dev/manual/latest.html#_sharing_a_local_cache ; Turborepo worktree cache: https://turborepo.com/docs/reference/configuration ; Bazel disk cache: https://bazel.build/remote/caching
- Conductor: https://www.conductor.build/docs/concepts/git-worktrees ; claude-squad: https://github.com/smtg-ai/claude-squad ; Uzi: https://github.com/devflowinc/uzi ; Vibe Kanban: https://vibekanban.com/docs/workspaces/repositories.md ; Gas Town: https://github.com/steveyegge/gastown ; Sculptor: https://github.com/imbue-ai/sculptor/blob/main/docs/help/workspaces.md
