---
name: harness-retro
description: End-of-session review that turns what went wrong or right this session into at most one regularized harness change (CLAUDE.md, rules, memory, skills, settings, tests) and prunes one stale piece. Run only when the user invokes /harness-retro.
disable-model-invocation: true
---

# Harness retro

Adapted from RRSI (Regularized Recursive Self-Improvement of Agent Harnesses,
arXiv 2609.24972). The finding that matters: a harness tuned on the work it
just saw gets better at *that* work and no better, or worse, at new work, while
growing more expensive. This session is the evolve set; every future session is
out of distribution. The job is to keep only changes that would transfer, and
to delete what has stopped earning its place.

"No change" is a normal, good outcome. Do not manufacture a lesson.

## 1. Evidence

From this session only, list what actually happened, with quotes:

- Corrections the user made, and what you had done.
- Wrong turns: time spent rediscovering something, a wrong assumption, a
  repeated failing command.
- Harness text that misled you (stale, wrong, ambiguous) or that you ignored.
- Harness text that demonstrably helped (cite it). This is credit for pruning.
- Where the time went: from the repo root, run
  `~/.claude/skills/harness-retro/time-report.py --since <session start>`.
  It reports work time (tests, builds), waiting time (CI, agents, the user),
  and CI time per job and step, across every session in the project. Agents
  that worked in another repo (e.g. a game repo) keep their transcripts in that
  repo's project dir: add `--project-dir ~/.claude/projects/<its dir>` for each,
  plus the default one. The
  biggest work rows are optimization candidates, and they're usually tests.
  A speedup is a repo change: propose it as a task, not as harness text.
- If this session orchestrated agents, their wrong turns are in their own
  transcripts, not this one. Find each agent's transcript (the report's session
  names; files are in the `--project-dir`), and give each to a read-only
  subagent in parallel: list that agent's wrong turns, repeated failing
  commands, rediscoveries, and harness text it tripped on or ignored, with
  quotes. Treat its findings as evidence like your own.

No evidence → skip to step 5 (prune) and stop.

## 2. Read the harness and the ledger

- Always-loaded context: every CLAUDE.md in scope (user, project, nested),
  `.claude/rules/`, the auto-memory `MEMORY.md`. Record its total bytes
  (`wc -c`). This is the cost every future session pays.
- On-demand pieces relevant to the evidence: skills, memory files, settings,
  tests and scripts that act as guards.
- The ledger, `<repo root>/.claude/harness-ledger.md` (create it on first
  write; outside a repo, use `<auto-memory dir>/../harness-ledger.md`). It is
  never auto-loaded; only this skill reads it.

Score open ledger entries against this session: did the failure an applied
change targets come up, and was it prevented (`hit`) or did it recur
(`miss`)? Append the date to that entry.

## 3. Propose and gate

For each candidate, state: component, the exact change, the failure it
prevents, and its evidence (this session + matching ledger entries).

Reject a candidate if any of these hold:

1. **Specific** — it encodes this session's file, bug, value or decision, and
   would not help on an unfamiliar task in this repo. That belongs in the
   commit message or the issue tracker.
2. **Inert** — it would not change what the agent does: restates code,
   generic advice the model already follows, a rule nothing checks.
3. **Derivable** — one grep, file read or `git log` answers it.
4. **Will rot** — exact counts, line numbers, version lists, file inventories.
   Rewrite as a qualitative statement or a command that computes it.
5. **Seen once** — a new always-loaded line backed by a single occurrence.
   One session is one noisy trial. Log it in the ledger as `seen 1×`; propose it
   when it recurs. Exception: a costly failure (data loss, destructive action,
   hours lost).
6. **Unbounded** — implies more checking, retries or confirmation with no exit.
7. **Already covered** — existing text says it. The problem is its placement
   or wording; edit that instead of adding.
8. **Previously rejected** — the ledger has it rejected or as a `miss`, and
   the approach is not materially different.

Survivors: put each at the cheapest place that would actually work. In order:
a test or script that fails loudly, a settings/permission change, a skill
(loaded on demand), a memory file, and only then always-loaded text. Text
skills and rules that only describe things tend to wash out. Make them concrete
and checkable, or back them with something executable.

Cost rule: every added always-loaded line must name the failure it prevents.
Changes that make always-loaded context smaller pass freely.

Budget: at most **one** addition per retro, so later retros can tell what
worked. Deleting or correcting stale facts doesn't count against it.

## 4. Optional independent critic

If a candidate passed narrowly, give a fresh-context subagent only the proposed
diff and the gate list above, not this session. A reviewer without the
session's context won't be swayed by it, which is where session-specific
lessons come from.

## 5. Prune one piece

Pick the always-loaded section or memory file the ledger shows was
least recently pruned. Verify each claim against the repo (run the commands;
do not trust the text). Delete what is stale, wrong, derivable, or has been
applied for five or more retros without a `hit`. Correct what is still useful.

## 6. Present, then apply

Show the user: the evidence, each candidate with its gate verdict, the
proposed diff, and always-loaded bytes before → after. Apply only what they
approve; harness changes are durable and may be shared with a team. Never
commit unless asked.

Then append to the ledger, one line per candidate, approved or not:

```
- YYYY-MM-DD · <component> · <change> · prevents: <failure> · <applied | rejected: reason | seen 1×> · hits:
- YYYY-MM-DD · pruned <section>
```
