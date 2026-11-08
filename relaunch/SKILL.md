---
name: relaunch
description: Hand off to a fresh session of yourself when your context runs high — write the handoff and your successor's brief, start the successor in a split of your Herdr tab, and it ends you. Use when a context-size warning tells you to hand off, when your brief says to relaunch, or when the user asks you to restart yourself.
---

# Relaunch

You are handing your lane to a fresh session, `<lane><N+1>`. It knows only what
you write down. Do the steps in order at a node boundary (or now, if the
warning says so). Start nothing new first.

## 1. Handoff: the state

Append to your handoff file (in an orchestrated wave,
`.claude/orchestrator/waves/<wave>/handoff-<lane>.md`) a block
`### <you> -> <successor> state (<time>)`:

- **PENDING FIRST:** what the successor does before anything else, with exact
  commands, branches and shas. In a swarm its first item is `swarm join
  --takeover` (with your `$SWARM_NAME`), so the swarm binds you to the
  successor's terminal before your pane dies; without it your death reaps
  your claims and locks. Then, always: "end `<your name>`
  (`hc kill <your $HC_TERMINAL_ID> && hc rm <your $HC_TERMINAL_ID>`) once
  `hc get <your $HC_TERMINAL_ID>` shows idle or done". The address is how it
  finds you (a session the user opened has no hc name); without it nobody
  closes your pane.
- In-flight work: running jobs (where, PID or queue entry, log path, how to tell
  it finished), open PRs, unrated pages, uncommitted work.
- Decisions made this generation and why, open questions, who decides them.
- Peers and their current names.

State is facts that change. It goes here, never in the brief. Don't commit
the handoff or the brief: they are local state for the next session on this
machine, not the repo's history (`.claude/orchestrator/` is gitignored).
Commit your own finished work first.

## 2. Brief: the standing harness

Copy your brief to `brief-<successor>.md` next to it and update the identity
line and the "read first" pointers (the handoff block above, then your
generation's section). Every generation reads the standing rules, so they cost
as much as always-on text. Gate them here:

- **Keep** a rule if this generation needed it (you would have gone wrong
  without it) or it guards a costly failure, and it is still true.
- **Drop** a rule about finished work, a fact the repo or docs now hold, a
  one-off value, anything a CLAUDE.md, skill or hook already says or enforces,
  and any copy of this procedure. One line does it:
  `At ~350k context, use the relaunch skill.`
- **Add** a rule only for a failure that cost real time this generation. Tag it
  `(new YYYY-MM-DD)`, and leave the tags on older rules alone.
- **Don't grow it.** If you add a rule, cut one. Compare `wc -c` of your brief
  and the new one, and report both numbers in step 3.

The brief's shape: identity and who's at the keyboard; read first; the first
jobs; standing rules; peers; the relaunch line.

## 3. Start the successor

Start it yourself, unless your brief says the orchestrator starts successors.
First finish or kill your background jobs (by PID), so your pane is safe to
close once you stop. Run from your working folder:

```bash
~/.claude/skills/relaunch/launch.sh <successor> split "Read and follow <brief path> (you are <successor>). First: in a swarm, run \`swarm join --takeover\` with SWARM_NAME=$SWARM_NAME. Then end <your name> (hc kill $HC_TERMINAL_ID && hc rm $HC_TERMINAL_ID) once \`hc get $HC_TERMINAL_ID\` shows idle or done. Then: <PENDING FIRST in one line>." <the flags you were started with>
```

It splits your tab, starts `claude -n <successor>` with the prompt as its first
message, and prints its address. The successor outlives you: a plain `hc run`
child would die when the successor ends you. Check it is working with
`hc get <successor>` (right after launch it can still show idle; `hc read
<successor>` if unsure), send the orchestrator, if any, `[from <you>]
relaunched as <successor>: <brief path> (brief bytes old → new)`, tell peers
its name, and end your turn. You then show as done, and the successor ends
you, which closes your pane.

If your brief says the orchestrator starts successors, send it `[from <you>]
handoff written: <brief path>, my address <$HC_TERMINAL_ID>` and end your turn.
It starts the successor, which ends you per the handoff's first item.
