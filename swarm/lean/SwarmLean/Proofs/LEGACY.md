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
`SWARM_PROOFS` is set. The `sorry`/axiom grep still covers every file. The proofs phase restores each import in
`SwarmLean.lean`, the two `check.sh` steps, and empties this list.
