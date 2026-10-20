---
name: relaunch
description: Hand off to a fresh session of yourself when your context runs high — write the handoff and your successor's brief, start the successor in a herdr pane, close your own. Use when a context-size warning tells you to hand off, when your brief says to relaunch, or when the user asks you to restart yourself.
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
  commands, branches and shas.
- In-flight work: running jobs (where, PID or queue entry, log path, how to tell
  it finished), open PRs, unrated pages, uncommitted work.
- Decisions made this generation and why, open questions, who decides them.
- Peers and their current names.

State is facts that change. It goes here, never in the brief. Then commit only
that file (`git commit -m "<lane>: handoff" -- <file>`), so you don't sweep up
other lanes' staged work. Commit your own finished work first.

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

If your brief or memory says you may relaunch yourself:

```bash
p=$(herdr pane split --current --direction down --cwd "$PWD" --no-focus | python3 -c 'import json,sys;print(json.load(sys.stdin)["result"]["pane"]["pane_id"])')
herdr agent start <successor> --kind claude --pane "$p" -- -n <successor> <the flags you were started with>
herdr agent prompt <successor> "Read and follow <brief path> (you are <successor>). <PENDING FIRST in one line>. Close <your name>'s pane once you are running."
```

Check that it is working (`herdr agent get <successor>`), tell peers and the
user its name in one line (brief bytes old → new), and stop. The successor
closes your pane once it is running. If it hasn't after a few minutes and
it's busy, close your own (`herdr pane close "$HERDR_PANE_ID"`) as your last
action.

Otherwise send the orchestrator `[from <you>] handoff committed: <brief path>`
and stop. It starts the successor.

A successor that finds its predecessor's pane still open, idle and with no
running jobs closes it.
