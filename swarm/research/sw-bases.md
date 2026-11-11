# sw-bases: per-task base branches, agent GC vs workspace GC

Status: implemented (boards #3 to #6, 2026-11-10), developed with the Lean TDD loop below. Theorems and findings are in
`swarm/model/SwarmModel/Workspaces.lean` and `Findings.lean`; see "Result" at the end.

## Problem (seen in the notapki formalization swarm)

1. The base is hardcoded to `main` / `origin/main`: `watchd.lua` lifecycle (`B = "main"`), `sweep_worktrees`,
   `conflict.lua` snapshot base, `ci.lua`; `brief.md` says work is done when it is "on main". A swarm landing on a
   local branch (`formal`) never sees work as landed: idle agents and their worktrees are never ended or swept.
2. Worktree ownership is inferred (`conflict.owned_wts`: dir `-<name>`, branch `<name>/…`, `agent.wt`). Agents make
   their own worktrees; one checked out the base branch itself, which blocked `git push . HEAD:<base>` for everyone.
3. `end_agent` couples a harmless act (kill the terminal) with a destructive one (remove worktree, `branch -D`), so
   ending must wait for the strictest check and is hard to allowlist.

## Design

- **Bases are data.** Repo default in `.claude/swarm.json` `{"base": "main"}`; per task `swarm task add --base <b>`
  (task column). One `base_for(task)` used by landed checks, conflict snapshots, the brief and CI (CI only for bases
  with a remote).
- **Agent GC (non-destructive).** End an agent when idle, no claim/lock/stay, and its task's commits are on that
  task's base. Ending = kill terminal only. `swarm end <agent> [--force]` is the manual trigger.
- **Workspace GC (refcounted).** Remove a worktree when no live agent is attached, no process cwd is inside, status is
  clean, and HEAD is reachable from a protected ref (any task base, `main`, `origin/*`). GC checks reachability
  itself: `git merge-base --is-ancestor <branch> <ref>` for each protected ref, plus the squash-merge content check.
  Then it deletes the branch, never a protected ref. As built (differs from the first draft, which said `branch -D`):
  `git branch -d` first, and when git refuses (it checks HEAD of the checkout, not our protected refs; in the notapki
  swarm `-d` from a checkout on `main` refused branches contained in `formal`) the sweep's own reachability check
  stands in and the delete is `git update-ref -d refs/heads/<br> <tip>`, which fails if the branch moved. Never `-D`.
- **Swarm-created worktrees.** `swarm spawn --task N` runs `git worktree add ../<repo>-<agent> -b <agent>/<task>
  <base>` and records `workspace(path, branch, base)`; agents link to it. Replaces `owned_wts` heuristics. Agents never
  check out a base; landing is a fast-forward of the base from a scratch branch (`git push . HEAD:<base>`, or a PR
  for a remote base). `swarm land` was not built: the communicator lands by PR or `git push . HEAD:<base>`.
- **Sharing.** Many agents may target one base. Many agents in one worktree only read-only (`--attach`): the index
  and build dirs (`target/`, `.lake`) collide.

## Method: Lean TDD (required)

1. State the theorem on the model (`swarm/model`).
2. Check the model still matches the current Lua (`replay.sh`, `lua/test/cli_model_spec.lua`).
3. Prove the current model violates it (a run in `Findings.lean`, fix off as a `Cfg` switch).
4. Fix the Lua.
5. Prove the theorem with the switch on (`check.sh`: no `sorry`, `native_decide`, axioms).
6. Re-replay: the model matches the new Lua; regenerate `traces/`.

Candidate theorems: (W1) a worktree is removed only if clean, unattached, no process is inside and its HEAD is
reachable from a protected ref (ancestor, or its content under a squash), and a deleted branch is never a protected
ref and its tip is reachable the same way; (W2) ending an agent removes no worktree or branch; (W3, fair runs) a landed, clean, unattached workspace is
eventually removed, and an idle agent whose task is on its base is eventually ended; (W4) no agent worktree has a
base branch checked out.

## Result

| Theorem | Statement | Refuted with the switch off | Proved with it on | Lua |
|---|---|---|---|---|
| B1 | lifecycle ends an agent only when its worktree is landed on a base of one of its tasks (main if none) | `not_B1` (finding #22) | `B1_of` (`perTaskBase`) | #3: `bases.lua`, `base_for`, `task add --base`, `.claude/swarm.json` |
| W1 | a worktree is removed only if clean, unattached, no process inside, HEAD reachable from a protected ref; a deleted branch is no protected ref and reachable | `not_W1_branch`, `not_W1_proc` (findings #18, #18b) | `W1_of` (`splitGC`) | #4: sweep checks itself; `delete_branch` |
| W2 | ending an agent removes no worktree and no branch | `not_W2` | `W2_of` (`splitGC`) | #4: `swarm end` and the lifecycle kill the terminal only |
| W3 | on fair runs a landed, clean, unattached workspace is removed and an idle agent whose work is on its base is ended | `not_W3_formal_wt`, `not_W3_formal_agent` (finding #20) | `W3_of` (`perTaskBase`, `splitGC`, `watchd`) | #3, #4 |
| W4 | no worktree has a base checked out | `not_W4` (finding #21) | `W4_of` (`recordedWorkspaces`) | #5: `swarm spawn --task` makes and records the worktree; a base checkout is refused |

`replay_W`: all five hold of `replay`, the instance the Lua replay runs (tasks 2 and 4 on `formal`). `Real.lean` ties the
Lua's decisions to the model's (`sweepGate_W1`, `landedRef_reach`, `endAgent_keepsGit`, `delRef_guarded`).

Findings beyond the design: `-D` was dropped for the guarded `update-ref -d` (above); `landed_ref`'s `gh` merged-PR check
ignores the base, so a PR merged into main makes a branch look landed on `formal` (board #43, open).
