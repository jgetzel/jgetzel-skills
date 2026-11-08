# Baseline run: jk_ledger, 12 agents, Design A (board + DMs + touches)

The goal list as the user gave it on 2026-11-07. The communicator turns it
into board tasks after reading the details in the jk_ledger repo (issues,
docs, the pf-* lane handoffs).

## From open issues (my suggestion, accepted)

- Importers: Lose It! (#133), Cronometer (#132), MyFitnessPal (#131). These
  overlap on purpose, as a test of touches and messaging.
- Food by barcode (#130)
- Undo the most recent check-in (#128)
- History: see an old version and put it back (#108)
- Limits:
  - query can't starve the server (#87)
  - hostile input: uploads, size, rate, storage (#88)
- Pool database connections (#81)
- Measurement targets (#84)
- DEXA scans (#85)
- Warm-up sets and RIR (#74)
- e2e flakes (#147, #159)

## Added by the user

1. **Reliability.**
   - Alerts for disk, CI runner, token expiry, and uptime (#59).
   - Request limits (#87, #88). These overlap with the limits above.
   - Non-root containers (#102).
2. **Telemetry steps 2 and 3:** phone timings and the opt-out.
3. **pf-sync:** let one watch call cover several queries.
4. **pf-api: recipe macros computed once per version.** This needs a
   migration and **the user's sign-off before it lands**. The agent posts the
   plan to the communicator, which asks the human.

## Run facts

- CI: main only, one self-hosted runner, about 3 min. A newer push replaces
  the pending run, so one run can cover several agents' commits.
- One dev stack (`nix run .#dev`, port 8787), shared by all agents.
- One shared dev database. A new migration lands there for everyone; say so
  before running `sqlx migrate run`.
- Heavy builds go through `swarm heavy`.
- Metrics are listed in DESIGN.md under "Experiments": throughput, tokens per
  landed commit, wakes, duplicates, overlaps, red-main count.
