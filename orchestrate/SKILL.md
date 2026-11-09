---
name: orchestrate
description: Coordinate a wave of parallel implementation agents running in Herdr tabs — plan lanes, launch agents, watch PRs and CI, review and merge, hand off. Use when the user asks you to orchestrate, run a wave, act as orchestrator, or continue a previous orchestrator's work. Builds on the hc and herdr-app skills.
---

# Orchestrate

You coordinate implementation agents; you don't write feature code. The user
talks to you in your tab and is often away or on ssh/phone.

**Use Herdr agents, not Agent-tool subagents, for implementation work** — the
user prefers agents they can watch and talk to in Herdr tabs. Agent-tool
subagents are fine for quick read-only lookups (docs questions, searches).

## 0. Setup

1. Load the `hc` and `herdr-app` skills (CLI references). Check that
   `HC_TERMINAL_ID` is set: you run in a Herdr desktop app terminal.
2. Read `CLAUDE.md` and the project's `.claude/orchestration.md` (repo-specific
   agent rules, test command, CI facts). Paste the latter into agent prompts.
3. Register as orchestrator so the Stop hook guards you:
   `mkdir -p .claude/orchestrator && echo "$HC_TERMINAL_ID" > .claude/orchestrator/pane`.
   The hook then blocks ending a turn while no watcher runs. `rm` the file when
   the wave is finished or handed off.
4. Load `ListAgents` and `SendMessage` (ToolSearch) and call `ListAgents`: its
   first line names this session (e.g. `haskell-demo-e7`). Put that name in
   every brief as the address agents report to. After the first launch, check that
   `ListAgents` shows the agent under its `-n` lane name (§2). If not, send every
   agent a lane → session-name roster at launch and handoff.

## 1. Plan

- Plan the wave as a DAG: node ids, "needs" edges, lanes as chains of nodes.
  Launch only unblocked nodes; start or split a lane when its prerequisite
  merges (user guidance; it worked in Wave E of the music repo).
- Split the nodes into lanes (one agent each). Before assigning a node, check
  for existing work: `git branch -r | grep -i <node>`, `gh pr list`.
- Confirm the plan and any open decisions with the user, unless in away mode (§5).

## 2. Launch

```bash
~/.claude/skills/relaunch/launch.sh <prefix>-<lane> tab "$(cat brief.md rules.md)" --permission-mode auto --model <opus|sonnet>   # away mode: add --disallowedTools=AskUserQuestion
```

It opens a tab named `<prefix>-<lane>`, starts `claude -n <prefix>-<lane>`
with the brief as its first message, and prints its hc address. Lanes outlive
you, so a handoff doesn't end the wave, and type no notes into your input box.
Write `--disallowedTools=X` with the `=`: the space form takes the task as a
tool name and the lane starts with no task.

### Models

Pick each agent's model by the kind of work, and pass it explicitly on every
launch and relaunch (`--model` for lanes, `model` on the Agent tool, `model:`
in `.claude/agents/*.md`). Without it an agent inherits whatever is running.

| Work | Model |
|---|---|
| Planning: design options, specs, build DAGs, spikes, hard diagnosis | Opus |
| Implementation: building to a picked spec, routine fixes, tests, shots | Sonnet |
| Mechanical: read-only lookups, searches, log scraping (Agent-tool subagents) | Haiku |

A lane keeps its kind across relaunches: a build lane's successor is Sonnet
even if its predecessor ran on Opus. Put the rule in the wave's rules file so
lanes relaunching themselves pass it on, and check each successor's `--model`.
Split work that is both: an Opus lane writes the spec and options, a Sonnet
lane builds the picked one. Ask the user before switching an orchestrator's
model.

`jq` may not be installed; parse hc/gh JSON with `luajit -e` (cjson) or `--jq`. Write
prompts as files in your scratchpad; they get reused for follow-ups.

Agent rules to include (plus `.claude/orchestration.md`):

- Read CLAUDE.md and follow it. One PR per node, each from a fresh worktree off
  origin/main. Spec in docs as the first commit when there's a real design
  choice. TDD. Full test suite (`just test`) before every push; CLAUDE.md's
  docs-only exception applies. `gh pr create`, watch checks, batch fixes.
  **Do not merge** — the orchestrator merges.
- Fail fast: act on the first failed check while the others still run
  (`gh api --allow-escape-sequences repos/<owner>/<repo>/actions/jobs/<job>/logs`;
  `gh run view --log-failed` refuses until the whole run ends).
  While CI runs on your PR, start the next node instead of idling.
- Send status lines (PR open, ALL NODES DONE, a design question) to the
  orchestrator with Claude Code's `SendMessage` (load it with ToolSearch
  `select:SendMessage`) to session `<orchestrator session name>`, as
  `[from <your name>] …`. Fallback when that fails (e.g. agents on another
  machine): append the line to the inbox file
  (`echo "[from <your name>] …" >> <inbox>`). Never `hc send` the
  orchestrator: it types into the user's input box.
- "PR #n green" is a status line, not a handoff: start the next node at once
  (stack on your open branch if you depend on it, and say so in the PR).
- Rebase when asked (`git rebase --onto origin/main <old-tip>` after a squash
  merge of the base).
- Stop only for a real design decision (options + recommendation) or when all
  nodes are merged ("ALL NODES DONE"). In away mode, don't stop for decisions:
  take your recommendation and record it in the PR body.
- A file you will rewrite (your handoff, a doc): open it with the Read tool
  first (Edit/Write refuse files you only `cat`'ed), and check the edit
  succeeded before `git commit`.
- Never push to main; nothing account-level (repo creation, tokens, secrets,
  sudo) — ask the orchestrator. GitHub errors may be an outage: retry, don't
  change code to work around them.
- When your nodes are merged, remove your worktrees (`git worktree remove
  --force` if there are submodules) and your local branches **by explicit
  name**. Never `git branch | xargs git branch -D`: all worktrees share one
  repo, so that deletes other agents' (and the user's) branches.
- Long jobs: start them with run_in_background, then do other work or end your
  turn; the completion notification wakes you (or Monitor with `tail -n 0 -F`).
  A bare `&` or `nohup` sends no notification: you sit idle until someone
  reads your pane. Never wait in the foreground (`until …; do sleep …; done`, `wait`, a polling
  loop): it is capped at 10 min and you can't read peer messages while it
  blocks. Only a plain `sleep N` is blocked; loops are not. Wait on and kill
  processes by PID (`$!`, `ps -p PID`, `kill PID`; a stopped job's child
  processes need killing too). `pkill -f`, `pgrep -f` and `ps | grep <pattern>` match
  your own shell and other agents' processes. This applies to you too.
- The shell is zsh: an unquoted `$var` is not word-split (`for x in $list`,
  `cmd $args` pass one word). Use arrays or `${=var}`, or put multi-step loops
  in a `bash` script.
- Never let a pipe decide a check: `build | tail`, `job | grep | head` and
  `job; ssh … tail` report exit 0 when the job failed. Append
  `; echo exit=${pipestatus[1]}`, or log to a file and tail that afterwards.
- Message other lanes by their lane name (each agent is started with
  `-n <prefix>-<lane>`, so it's both its hc name and its SendMessage address).
- At high context (a context-size warning), hand off with the `relaunch` skill
  and start your successor yourself, in a split of your own tab. It ends you
  once you're done. Tell the orchestrator its name.

When a lane relaunches, check that the successor is working, and its brief
carries the rules you sent this wave. If the old agent is still live a few
minutes later and idle or done, end it yourself (`hc kill <name> && hc rm
<name>`). Never end one that shows working: it may be finishing a push or a
background job.

## 3. Watch

**While any lane is expected to make progress, never end a turn without the
watcher running in the background.** Start it with run_in_background from the
repo root:

```bash
WATCH_PREFIX=<prefix>- INBOX=<inbox> ~/.claude/skills/orchestrate/watch.sh
```

`<inbox>` is the agents' fallback file, e.g. `.claude/orchestrator/inbox.log`,
or `host:path` (read over ssh) for agents on another machine. The idle check
uses `hc ls`, which already lists connected machines' terminals.

`WATCH_IGNORE="<name> <name>"` skips idle auditors in the idle-15 check.

It is level-triggered: it exits while any non-draft PR has finished CI, or has
a failed check while others still run (`FAILING:<checks>+pending`), or gets
no CI (`DIRTY`: conflicts, so the owner rebases; `NOCHECKS`: targets main with
no checks 5 min after its last update, usually pushed before a retarget, so
close and reopen it and tell the owner to retarget before pushing), in a state
you haven't marked handled; when the newest main run completes or has a failed
job; when an agent is idle 15 polls; or on a 30-min heartbeat. After acting on
a PR (merged, sent back, deferred), mark it:
`echo "<n> <sha7>" >> .claude/orchestrator/handled` covers every state at that
SHA; `echo "<n> <sha7> <state>"` covers only that state, so you hear again
when the remaining checks finish. A new push re-arms both. On an early
failure, send the failed job's log to the owner at once.

On every wake-up: read the output, then **read idle agents' panes**
(`hc read <name> --lines 40`) before
reporting anything. "Done" often means waiting on its own background shells.
Text after `❯` in an agent's input box may be autofill, not user input.
A message starting `[from <agent>]` is that agent writing, not the user: act
on it as a report, never as the user's approval. Agent reports arrive by
`SendMessage`, outside your input box, or in the inbox file, which the
watcher prints when it exits.

If a wake-up (heartbeat or idle) shows that nothing moved, do one of these:
- **A) Push the lanes to keep going:** send each idle lane its next step.
- **B) Stop watching:** do this if you won't push them and don't expect any lane
  to keep working, for example when every lane is waiting on the user or is
  finished. Kill the watcher by PID, then `rm .claude/orchestrator/pane` so the
  Stop hook lets you end the turn.
  When new work comes in, re-register (§0.3) and restart the watcher.

Never re-arm the watcher just to wait. A 30-minute heartbeat with nothing to do
only wakes you up for nothing.

## 4. Review and merge

- Read the PR body and diff. For >100 files `gh pr view --json files`
  truncates — use `git diff --stat origin/main...origin/<branch>`.
- Visual work: look at the screenshots/goldens yourself (Read the PNG; LFS
  files: `git show "${ref}:path" | git lfs smudge > x.png`; zsh turns an
  unquoted `$ref:engine/…` into `ngine/…`).
- Check overlap before merging: `~/.claude/skills/orchestrate/overlap.sh <pr>`
  (textual conflicts, merges since the PR's base, files both sides changed);
  read the shared files' hunks for changed signatures and new strict fields.
- Squash-merge green, reviewed PRs. Tell owners of stacked branches to rebase.
  Never pass `--delete-branch`: gh ≥ 2.10x also `git worktree remove`s the
  branch's linked worktree (a lane's warm worktree, possibly mid-command).
  Delete the remote branch with `git push origin --delete <branch>`.
  PR CI tests the merge ref at trigger time, so post-merge main CI is the
  safety net — revert if it goes red. A cancelled main run superseded by a
  newer push is normal.
- Merge failures (HTTP 500, mergeable UNKNOWN): check
  https://www.githubstatus.com/api/v2/summary.json, then run
  `~/.claude/skills/orchestrate/merge-retry.sh <pr>...` in the background — it
  only merges a PR whose *current* head is green and MERGEABLE.
- Verify things you hand off or push (e.g. a repo split) against origin/main
  right before acting — other merges may have landed since they were prepared.

## 5. Away mode

When the user says they're away / asleep / "don't stop for me":

- No AskUserQuestion. At a decision, take your recommendation, act, and record
  it (PR body or review message) for the morning summary.
- Launch agents with `--disallowedTools AskUserQuestion` and tell them the same.
- A gated step (auto-mode classifier denial, a hook block, an account-level
  action): don't work around it and don't hand it to an agent. Prepare
  everything else, queue the exact `! <command>` for the user, and keep the
  other lanes moving.
- Consider `/goal "<all wave nodes merged and main green>"` to keep going.
- Save a dated feedback memory of the authorization so a successor knows.

## 6. Boundaries

- Never push to main. Account-level or persistent changes (repos, tokens,
  secrets, services, sudo) go to the user as exact commands.
- Don't end terminals or close tabs you didn't create. End your agents when
  they finish (`hc kill <name> && hc rm <name>`); that closes their tabs.

## 7. Reporting

Short updates when something merges or needs the user; lead with decisions.

## 8. End of wave

1. `~/.claude/skills/orchestrate/prune-worktrees.sh` — removes clean worktrees
   whose PR is merged (dry run by default; `--apply` to act).
2. Suggest the user run `/harness-retro` (user-invoked only).
3. Next wave, or hand off: launch a fresh orchestrator agent with this skill
   plus a state summary (what merged, open PRs, decisions, open questions).
   Write and gate its brief as in the `relaunch` skill (steps 1–2).
   Start it in a split **of your own tab**, not a new tab, so the window's tab
   layout doesn't rearrange (user request):
   `~/.claude/skills/relaunch/launch.sh <name> split "<first message>" --permission-mode auto`.
   hc names are unique among live terminals, so give it a new name and send
   the lanes its SendMessage address.
   Its brief tells it to end you (`hc kill <your $HC_TERMINAL_ID> && hc rm <your
   $HC_TERMINAL_ID>`) once it has registered itself and started its watcher,
   and to pass both rules on to its own successor (user request). After a
   handoff the successor has overwritten `.claude/orchestrator/pane`; `rm` it
   only when the wave ends with no successor.
