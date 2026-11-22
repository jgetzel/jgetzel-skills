# Proofs out of the build (sw-global §3)

Proof files that stopped compiling while the store moves to statements leave the build (their imports out of
`SwarmLean.lean`, their names out of `comparator.json`, `Challenge.lean`/`Solution.lean` and `Audit.lean`'s
expectations) and are listed here with the commit that dropped them. The proofs phase (board #79 to #82) brings each
back in the new shape, or replaces it, and empties this list.

| File | Dropped by | Why |
|---|---|---|

None so far: the foundation (board #68) kept every proof in the build. `Proofs/Watchd.lean`'s fate correspondence
now runs with `Decide.Facts.ours` always true (a terminal in another repo is no longer foreign).
