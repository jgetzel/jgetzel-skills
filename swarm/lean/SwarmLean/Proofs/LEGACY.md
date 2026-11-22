# Proofs out of the build (sw-global §3)

Proof files that stopped compiling while the store moves to statements leave the build (their imports out of
`SwarmLean.lean`, their names out of `comparator.json`, `Challenge.lean`/`Solution.lean` and `Audit.lean`'s
expectations) and are listed here with the commit that dropped them. The proofs phase (board #79 to #82) brings each
back in the new shape, or replaces it, and empties this list.

| File | Dropped by | Why |
|---|---|---|
| `SwarmLean/Proofs.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/Tasks.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/Locks.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/Msgs.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/Watchd.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/Cross.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/Sweep.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/Trust.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/WriteBack.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/Migrate.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/Queue.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/Crash.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |
| `SwarmLean/Proofs/Keep.lean` | board #84 | all proofs out at once (user's call, 2026-11-21): land the store work first |

With them: `Audit.lean` and `challenge.sh` (Challenge.lean, Solution.lean, comparator.json) are skipped by `check.sh` unless
`SWARM_PROOFS` is set.

Within `Proofs/Crash.lean` (out of the build already), board #69 removed `hook_keeps`: the hooks run on the statement
store (`Store.run`), and `keeps_walk` has no step for a `Txn`. `groups_keep` takes the hooks' case as a hypothesis (`hH`)
until the statement lemmas (#79) and the agents/messages WF proofs (#81) give it back; `keeps_view` covers `Store.view`. The `sorry`/axiom grep still covers every Lean file. The proofs phase restores each import in
`SwarmLean.lean`, the two `check.sh` steps, and empties this list.

One watchd per machine (board #75) leaves the proofs phase two things: `RecM`'s `Scoped` instance runs another scope
on the same `Db` (`Assumptions.lean`: the model has one store), so `pass_keeps` covers watchd's per-swarm and per-repo
loops only as if every scope were one db; and `Watchd.sweep`'s new `made` filter (only `workspace`-made worktrees) is
one more skip condition for `sweep_W1` and the keep proofs. #81/#82 state and prove that watchd never moves a live
binding (`Cmd.Watchd.ensureComms` binds only when `commsPresent` is false, re-read after the launch, and with
`bindAgent`'s takeover off).
