# swarm-retro research: regularized retrospectives for swarm and single-agent runs

Researched 2026-11-07. Question: what should an end-of-run retrospective for a peer swarm (shared
board, messages, touches, locks, no manager) do to turn a run into a few durable, regularized
changes to user skills, repo skills and repo docs, and stay usable for a single-agent session?

**Method and confidence.** RRSI and Harness² were read through WebFetch, which returns a
model-written summary, so their numbers are as that summary reported them. I also cloned both
code repos and read the prompts directly.

Tags: **[code]** quoted verbatim from those repos; **[abs]** from an arXiv abstract page only;
**[unverified]** from a search snippet or secondary page.

The OpenAI harness-engineering post returned 403. Prior multi-agent art (`sw-prior.md`) and swarm
failure modes (`sw-pitfalls.md`) are not repeated here.

## TL;DR

- **Both papers gate on execution, not on how good an edit sounds.** RRSI scores each candidate
  over k trials and accepts it only above a measured noise band, and only if the gain pays for
  the cost. Harness² replays the task under each candidate and keeps what a behavioural contrast
  supports.
- **Regularization buys transfer, not evolve-set score.** Unregularized evolution scored 92.8
  on the evolve split and 40.3 OOD at 3.80M tokens per trial; RRSI scored 90.5 and 43.6 at 2.42M
  ([RRSI](https://arxiv.org/abs/2609.24972), Table 2). The edits that transferred were structural
  and free of task vocabulary.
- **Self-written skills are about worthless by default.** Curated skills gave +16 pp, self-written
  ones about 0. Focused skills of at most three modules beat exhaustive ones
  ([SkillsBench](https://arxiv.org/abs/2602.12670), [Ratchet](https://arxiv.org/abs/2605.22148)).
- **Harness evolution often loses to "just run it again".** Under matched budgets it "fails to
  outperform simple test-time scaling methods"
  ([2607.12227](https://arxiv.org/abs/2607.12227)). Rule out variance before blaming the harness.
- **Multi-agent blame by LLM is unreliable.** It finds the right agent 53.5% of the time and the
  decisive step 14.2% ([Who&When](https://arxiv.org/abs/2505.00212)). Use the deterministic event
  log, quote the step, and say `confounded` when unsure.
- **Coordination failures are a tooling problem first.** A shared claim log cut duplicate work
  from 78% to 0% ([grite](https://arxiv.org/abs/2606.19616) [abs]). Paired agents did about 30%
  worse than solo agents ([CooperBench](https://arxiv.org/abs/2601.13295)). Fix the CLI, the
  watcher or a hook before adding brief prose.
- **Placement is mostly decided by kind.** A verified repo fact goes in repo docs, a procedure
  in a skill with a trigger, a mechanical rule in a hook or script. Always-on text comes last:
  "if you add some, cut some" (Harness² [code]; [Claude Code docs](https://code.claude.com/docs/en/memory)).
- **The current `harness-retro` has five gaps:** no retry or variance check; no check for
  success habits an edit could break; a "Specific" gate that rejects verified repo facts; no
  check that a new skill is reachable; and pruning that conflates "the cue never came up" with
  "the piece didn't help".

## 1. The primary papers

### 1.1 RRSI: Regularized Recursive Self-Improvement of Agent Harnesses (arXiv 2609.24972; v1 21 Sep 2026, v3 4 Oct 2026; Google)

**Loop.** Each round runs Analyze → Propose → Screen (critic) → Evaluate (full evolve set, k
trials per task) → Select → Record ([HTML](https://arxiv.org/html/2609.24972v3)).

- The analyst never reads raw traces. It sends read-only digesters out and aggregates three
  lenses: `failure_modes`, `capability_gaps` and `success_habits`. The last is "kept across
  rounds as a regression guard for the proposer" [code: `rrsi/analyst.py`].
- Descriptions "must be entity-free and task-agnostic". The analyst must "Keep prior mode names
  when the same mechanism recurs" and must "NOT attribute blame to model vs scaffold" [code].

**What's edited.** Any component: prompt, control_flow, config, output_plumbing, context_mgmt,
client_tool, skill, memory or subagent. The policy is frozen.

**What every edit must declare** [code: `rrsi/propose.py`]: `hypothesis`; `why_not_lower_lever`;
`trigger_condition`, "the exact, checkable condition under which the mechanism activates
('always' is almost never right)"; `predicted_affected` task ids, scored afterwards
("over-claiming counts against you"); `retroactive_check`, "(corrective) … (preservative) which
success habits could this disrupt … (transfer) why it generalizes beyond this evolve set"; and
`regression_risk`.

**Proposal regularizers.** The edit budget anneals by cosine from b_max (3–4) to b_min = 1,
"so late-round measurements attribute to a single component". On a stall, one candidate slot is
reserved for components never tried.

**Selection regularizers** [code: `selection.py`, `critic.py`]:
- **Critic.** Claude Opus 4.8 screens every candidate before any evaluation is spent. It
  rejects leakage or task specialization (litmus test: "would this change still make sense, and
  still help, on an unfamiliar task from a different suite in the same kind of work?"),
  degenerate or no-op edits and deleted safety mechanisms, grader gaming, undeclared bundling,
  memory or skill mechanisms that persist task-specific runtime data, and "UNBOUNDED WORK: an
  added check, retry or 'keep improving' loop with no give-up path".
- **Noise floor.** δ is measured by re-running the unchanged base harness. A candidate needs
  S′ ≥ S* − δ. The paper calls δ "the one value that must not be tuned".
- **Cost rule.** Above noise, ΔC ≤ β₀ + β₁·ΔS. Within noise, "a neutral candidate survives by
  cutting tokens or by landing a working, non-regressing structural mechanism, never by a
  coin-flip gain" [code: `domains/workspace/SKILL.md`].
- **Pruner.** It removes components that were *exercised* and whose best gain over the last 4–5
  rounds is ≤ 0. Never-exercised components are flagged for exploration, not deletion [code:
  `history.py`].

**Evaluation.** Evolve on Terminal-Bench 2.1, Harvey LAB and EngDesign; hold out SWE-bench
Verified, LAB-ID, JobBench, GDPval, APEX-Agents and Frontier-Eng.

**Results.**
- Gains reach +6.0 on the evolve set and +4.3 out of distribution, and "no held-out split
  regressed".
- OOD averages (Table 1): RRSI 43.6, base H₀ 39.7, Meta-Harness 40.6, TTHE 38.0.
- The four accepted RRSI edits were structural probes, such as reading back the deliverable,
  and named no task vocabulary.
- Meta-Harness and TTHE piled up standing text fitted to the scorer. TTHE ended 1.7 points below
  its start out of distribution.
- Ablation (Table 2): removing the acceptance-side regularizers costs 2.6 OOD points, the
  proposal side 1.7. The critic, budget and pruner are not isolated individually.
- Rejected examples: +1.69 points at +26% cost, rejected by the cost rule; and −13.6% cost at
  −2.81 points, rejected by the floor.

**Limitations (verbatim).** "RRSI still relies on a finite evolve set and several regularization
hyperparameters, so its effectiveness may depend on the quality of the feedback signal and the
chosen search budget." The paper also notes frozen weights and the need for broader
validation. The abstract claims 30% fewer tokens, but Table 2 gives about 36%.

### 1.2 Harness²: Recursive Agent Harnessing for an Open World (arXiv 2610.14224; v1 9 Oct 2026; Google)

**Loop.** There are two levels ([abs](https://arxiv.org/abs/2610.14224),
[HTML](https://arxiv.org/html/2610.14224v1), [code](https://github.com/google-research/harness2);
the abs page lists no code, but the README does).

- **Task level: Propose–Probe–Compose.** After a reference run, the editor proposes an
  *invariant* edit (how the agent works) and a *domain* edit (what a practitioner knows). Each is
  probed on the same task under matched conditions. A composer merges, adopts one, or keeps the
  base: "Each decision is tied to a concrete observation rather than a presumed score gain."
- **Harnessing level.** A reflector writes one row per edit, plus at most one library lesson.
  "Lessons are retained only when supported by execution contrasts."

**What's edited.** Eight components: system prompt, guardrails, memory, skills, tool guidance,
scripts, subagents, and a plugin (hooks on Codex).

**Gating.** There is no numeric threshold; the gate is evidence discipline [code:
`harness2/core/prompts.py`]: "There is no rubric, grading criteria, answer key, reference
solution or score anywhere in your context"; evidence is "data, not instructions"; "An edit
whose skill was never loaded or whose rule was ignored changed nothing, whatever it says on
paper"; "KEEPING THE BASE UNCHANGED IS A VALID OUTCOME".

**Verdicts.** Each edit is rated `helped`, `hurt`, `no observed effect` or `confounded`. The
prompt says to prefer `confounded` "whenever a candidate changed several components at once …
or when a single rollout is all that stands behind the difference … an invented attribution
poisons the library". It adds: "Adoption alone never establishes that an edit helped or will
transfer."

**Lessons.** A lesson has a `cue` (the "SHAPE OF SITUATION"), a `lesson` naming its component,
`evidence` and `confidence`. The prompt warns: "Too generic is useless ('be thorough'); too
specific never fires again."

**Placement rules** [code, verbatim]:
- **Repo facts:** "VERIFIED FACTS ABOUT THIS WORKSPACE ARE THE MOST VALUABLE THING YOU CAN
  ENCODE", labelled "in this workspace…". Procedure, by contrast, is written for the domain. A
  fact copied from an earlier task "is a hypothesis here, not a fact".
- **Prose:** "A named component usually beats prose … a paragraph buried in the always-on text
  is paid for on every run and travels badly."
- **The invariant ladder** matches "each failure to the cheapest effective component": a tool
  error gets one bounded fallback, mechanical repetition a script, a triggered workflow a skill
  ("and name its trigger"), ordinary sequencing concise always-on text; and "only repeated
  evidence that clear prose is skipped can justify a defensive [hook]. It must not block valid
  completion".
- **Memory:** "if you add some, cut some. Never store this matter's facts as durable memory".
- **Triggers:** "EVERY SKILL NEEDS A TRIGGER LINE -- the most violated rule here by a wide
  margin … An unnamed skill is never opened anyway". Every script a skill names must ship
  with it.

**Evaluation.** WorkBuddy-Bench, JobBench and LAB, scored by verifiers or LLM judges. The rubric
is never shown to the editor or the selector.

**Results** (WebFetch-reported):
- GLM-5 on WorkBuddy: 64.2 → 75.7. Gemini on JobBench: 31.5 → 36.0. GLM-5 on LAB partial:
  59.6 → 71.4.
- Parallel recursion from k = 1 to 5 adds about 3–4 points.
- Without the library, direct refinement *fell* (Code 73.4 → 63.2).
- Removing skills hurt most on Code and Web; removing scripts hurt most on Office. The effects
  were not additive.

**Limitations.** Verbatim: execution feedback does "not guarantee correctness or establish that
an adopted change will transfer to a different task", and "Increasing test-time exploration
alone therefore does not ensure better performance". Also reported: selection bias (an output
scoring 55 chosen over one scoring 95), false premises spreading through the library, library
and context bloat, and uneven transfer (GLM-5 +17.3 on Code, Opus 4.8 +2.6). A "w/o scoping"
ablation row appeared in one fetch only [unverified].

### 1.3 Newer and related work (2026)

| Work | Date | What it adds for a retro |
|---|---|---|
| [Rethinking the Evaluation of Harness Evolution](https://arxiv.org/abs/2607.12227) | Jul 2026 (v4 Oct) | At matched budget, harness evolution doesn't beat test-time scaling on Terminal-Bench 2.1 and generalizes poorly. It wins on long-horizon games (+80% ARC-AGI-3). Compare an edit against a plain retry. |
| [SkillEvoReg](https://arxiv.org/abs/2609.30861) | 25 Sep 2026 | Names "skill-evolution overfitting". Causal counterexample validation builds an attack on a case the incumbent handles, aimed at the assumption the candidate changed. Complexity control edits only touched atoms (NoOp, Merge, Rewrite, Delete). Ablation: 31.7K → 11.7K chars while the score rose 47.0 → 59.25 ([HTML](https://arxiv.org/html/2609.30861v1)). |
| [Ratchet](https://arxiv.org/abs/2605.22148) | May 2026 (v3 Aug) | Retire skills on measured contribution and cap library width. A judge that passes failures at rate ≥ (1−τ)/2 "retires nothing, at any sample size". Ungoverned libraries grow until a skill scores worse than none [abs]. |
| [SkillsBench](https://arxiv.org/abs/2602.12670) | Feb 2026 (v4 Jun) | Curated skills raise pass rates 33.9 → 50.5%. Focused skills of at most three modules beat exhaustive bundles. The self-generated ≈0 figure is from Ratchet and summaries, not the abs [unverified]. |
| [Meta-Harness](https://arxiv.org/abs/2603.28052) | 30 Mar 2026 | The proposer reads full prior traces, code and scores from a filesystem. Strong in domain, but RRSI shows it overfits the scorer. |
| [TTHE](https://arxiv.org/abs/2607.08124) | Jul 2026 (v3 Nov) | Evolves the harness at test time from unlabelled traces; RRSI reports it falls below its start OOD. |
| [Meta-Team](https://arxiv.org/abs/2605.29790) | May 2026 (v2 Oct) | Multi-agent self-evolution. It preserves each agent's context and runs post-task communication to "exchange distributed evidence". Edits go to the agent, coordination or team level [abs; no numbers on the page]. |
| [Cursor: harness](https://cursor.com/blog/continually-improving-agent-harness) | 30 Apr 2026 | Online A/B tests and "Keep Rate". Per-tool, per-model error alerts. A weekly automation files tickets. Guardrails were removed as models improved: static context is "mostly long gone". |
| [Cursor: Bugbot](https://cursor.com/blog/bugbot-learning) | 8 Apr 2026 | Rules start as candidates, are promoted on accumulated signal, and are disabled on "consistent negative signal". |
| [OpenAI: Harness engineering](https://openai.com/index/harness-engineering/) | 11 Feb 2026 | 403. Snippets say one big AGENTS.md drifted because nothing checked it, and was replaced by a ~100-line map into `docs/` [unverified]. |

## 2. What's specific to multi-agent runs

**Credit assignment.**
- LLM attribution is weak. On Who&When, the best method found the responsible agent 53.5% of
  the time and the decisive step 14.2%, and reasoning models didn't fix it
  ([2505.00212](https://arxiv.org/abs/2505.00212)). 2026 follow-ups (AgentLocate 2607.07989,
  FALAT 2606.00765) improve step accuracy only to tens of percent [unverified].
- BLADE (Oct 2026) audits each handoff and labels each agent as having **introduced,
  propagated or repaired** an error. It beats all-at-once judging by 2.2–11.1 pp
  ([abs](https://arxiv.org/abs/2610.18780)).
- "Model or Harness?" (Jul 2026) gives each failure a *fault side*: model, harness, or
  environment/grader ([abs](https://arxiv.org/abs/2607.28802)).
- For the retro: edit instructions only for harness-side faults, fix at the agent that
  introduced the error, treat propagation as a missing check at the receiving handoff, and route
  environment faults to repo tasks.

**Parallel agents as repeated trials.**
- RRSI's gate depends on k trials and on a δ measured with the harness unchanged. Swarm agents
  doing the same kind of step under the same brief are such trials, and they cost nothing
  extra. Their spread is the run's noise band, so 1 of n is within noise.
- The trials are not independent, though. Same-model peers conform (18 of 30 chose the same
  branch name, `sw-prior.md` §1.5), and they read each other's posts. An agent that copied a
  peer's approach from a message is not a new trial. Count only agents that diverged *before*
  they saw each other's work.
- Treat one agent's outcome as one rollout, which is `confounded` in Harness² terms.
- If a retry or another agent got it right under the unchanged harness, that is variance
  ([2607.12227](https://arxiv.org/abs/2607.12227)).

**Detecting coordination failures.** Do it by script over `swarm.db`, which per
`swarm/DESIGN.md` holds an append-only `event` table plus `agent`, `msg`, `cursor`, `task`, `touch` and `lock`.
grite mines a similar log for "conflicting edits, lock starvation, redundant rediscovery, and
race-to-close" ([abs](https://arxiv.org/abs/2606.19616)). Signals to compute:

- **Duplicate work** (same file touched or equivalent tasks closed without a claim);
  **conflicts** (overlap events, failed merges or rebases, CI reds caused by a peer).
- **Lost messages** (a read cursor never passes it, or a directed post gets no reply or action);
  **idle agents** (idle while unclaimed tasks are open).
- **Stale claims** (a lease held with no touches, or expired); **lock waits**; **race-to-close**
  (a task closed twice or reopened).
- **Broken commitments and expectation errors** ([CooperBench](https://arxiv.org/abs/2601.13295)
  categories): an "I'll do X" with no X in the log, or a plan premised on a peer state the log
  contradicts. These need an LLM, but each finding must cite a log event.

**Whose instructions to change.** Meta-Team separates agent, coordination and team edits. Combine
that with fault side and origin:

| Evidence | Change |
|---|---|
| A coordination failure the substrate could prevent or flag | Swarm tooling (CLI, watchd, hook). Prose last. |
| The same failure in ≥ 2 independent agents under one brief | The shared brief, or the skill it loads |
| 1 of n agents, the others fine | The ledger only (`seen 1×`), or that role's brief if its role differs |
| An error propagated across a handoff | A check at the receiving step (often a script) |
| An environment or repo fault (flaky test, missing script) | A repo task, not instructions |
| The communicator mis-split work or left "done" unclear | The swarm skill's communicator section |

## 3. Where an edit goes, and what form sticks

**Ladder.** Take the first rung that fits.
1. **Mechanical and checkable at a tool call → hook.** Claude Code treats CLAUDE.md "as context,
   not enforced configuration. To block an action regardless of what Claude decides, use a
   PreToolUse hook" ([docs](https://code.claude.com/docs/en/memory)). Harness² adds that only
   repeated evidence of skipped prose justifies a hook, and it must not block valid work.
2. **Repeated deterministic work → script.** In a swarm, that script is often the swarm CLI
   itself.
3. **Narrow procedure with a recognisable trigger → skill.**
   - User-level if it is the same kind of work in any repo; repo-level if it relies on this
     repo's layout.
   - Its `description` is the trigger. A `disable-model-invocation` skill must be named
     wherever agents read (Harness² trigger rule).
4. **Verified repo fact not one grep away → repo doc.** Put it in a `.claude/rules/` file
   scoped to its path, or in CLAUDE.md or AGENTS.md, labelled as a repo fact (Harness² "in this
   workspace…").
5. **Short universal fact → always-on text.** Keep CLAUDE.md under 200 lines ("longer files …
   reduce adherence"), resolve contradictions, and pair every addition with a cut.
6. **Per-agent brief → role scope only.** A rule repeated across two or more briefs moves to a
   skill.

**Scope.** Apply RRSI's litmus test per scope. A user-level change must help in an unfamiliar
repo. A repo-level change must help on an unfamiliar task in this repo. Evidence from one repo
doesn't justify a user-level change, unless the defect is in that user skill's own scripts or
text.

**What sticks:**
- **Hooks and scripts over prose.** Prose is advisory: "there's no guarantee of strict
  compliance, especially for vague or conflicting instructions" (docs).
- **Structured files over Markdown for state agents shouldn't rewrite.** Anthropic used JSON
  because "the model is less likely to inappropriately change or overwrite JSON files compared
  to Markdown files"
  ([Effective harnesses for long-running agents](https://www.anthropic.com/engineering/effective-harnesses-for-long-running-agents);
  2025, exact date not in fetch).
- **Structural, vocabulary-free edits transfer.** In RRSI they did and prose-heavy ones
  overfit. In Harness² ablations, skills and scripts carried the largest effects.
- **Self-written skill text gives about +0; focused curated skills help** (SkillsBench, Ratchet).
- **Pruning is half the job.** Ungoverned libraries degrade (Ratchet). SkillEvoReg cut skill
  size about 2–3× with held-out scores mostly held. Cursor dropped guardrails as models improved.
- **Built-in checks.** `/doctor prompt-audit` (Claude Code ≥ 2.1.283) reports stale,
  contradictory or dangling instructions across CLAUDE.md, AGENTS.md, rules and skills. The
  `InstructionsLoaded` hook logs which instruction files actually loaded (docs).

## 4. Gaps in the current `harness-retro`, against the papers

1. **No variance check.** Gate 5 counts occurrences but has no noise test. RRSI measures δ with
   the harness unchanged, and 2607.12227 shows a retry often matches an evolved harness. Add:
   "Would a retry, or another agent, have done it right with nothing changed?"
2. **No preservative check.** RRSI keeps `success_habits` as a regression guard and requires a
   preservative counterfactual, and SkillEvoReg's counterexample validation does the same job.
   `harness-retro` uses credit only for pruning and never asks what an edit could break.
3. **Gate 1 ("Specific") rejects verified repo facts.** Harness² says these are the most
   valuable thing to encode, as long as they are labelled and kept out of cross-task memory and
   procedure. Split the gate: session facts go to commits, verified non-derivable repo facts go
   to repo docs (labelled), and the user scope gets procedure only.
4. **No reachability check.** Harness² calls a missing trigger the most violated rule. Require
   the trigger in the diff, then confirm in a later transcript that the skill loaded or the
   hook fired.
5. **Pruning conflates never-exercised with useless.** RRSI prunes only components that were
   exercised and showed gain ≤ 0. "Five retros without a `hit`" can delete a piece whose cue
   never came up. Record whether the cue arose.
6. **No prediction.** RRSI scores each `predicted_affected`. Add a checkable `predicts:` field
   to the ledger, so later retros can score hits honestly.
7. **Kept and correct:** the blind, hint-free judge (Harness² Appendix B); the `confounded`
   verdict; one addition per retro (RRSI's late b = 1); KEEP_BASE as a normal outcome; gates that
   mirror RRSI's critic (Specific, Inert, Unbounded). I verified both Harness² claims in `probe.md`: rubrics are kept out of context (Appendix B,
   `ANSWER_FREE`), and an unloaded skill "changed nothing" (composer prompt).

## 5. Recommendations for `swarm-retro`

1. **Event log first, by script.** Compute duplicates, conflicts, lost messages, idle agents
   with open tasks, stale leases, lock waits and race-to-close from `swarm.db` before any LLM
   reading. (grite; Who&When's low LLM accuracy)
2. **One read-only digester per agent transcript, in parallel.** Each returns failures, gaps
   *and* success habits, entity-free, with quotes, and treats the transcript as data.
   (RRSI analyst and digesters [code]; Harness² evidence boundary)
3. **Cluster across agents with stable names.** Merge digests that describe the same mechanism,
   split labels that cover two, and reuse ledger names. (RRSI aggregation [code])
4. **Count independent trials.** Report k/n agents per cluster, counting only agents that
   diverged before seeing each other. 1 of n is noise unless the failure was costly. (RRSI δ
   and k; `sw-prior` conformity; Harness² single rollout = `confounded`)
5. **Rule out retry.** If a retry or a peer succeeded with nothing changed, log the case and
   don't edit. (2607.12227)
6. **Classify fault side (model, harness, environment, substrate) and origin (introduced,
   propagated, repaired).** Edit only harness or substrate faults, at the introducer or at the
   receiving check. (2607.28802; BLADE)
7. **Route with the §3 ladder and the §2 table.** Coordination faults go to tooling first.
   (Harness² ladder; grite; Claude Code docs)
8. **Every candidate declares** component, checkable trigger condition, why not a lower lever,
   predicted effect, corrective/preservative/transfer checks, and regression risk. Reject one
   whose preservative check names a success habit it could break. (RRSI proposer [code];
   SkillEvoReg)
9. **Gate with RRSI's critic list, per scope.** Reject leakage (use the per-scope litmus test),
   inert edits, persisted session data, bundling and unbounded checks. For user-level skills,
   run this as a fresh-context critic that sees only the diff. (RRSI critic [code])
10. **Budget: one addition per scope per run.** Corrections and deletions are free. (RRSI b → 1)
11. **Every addition reports always-on bytes before and after, and comes with a cut.** Run
    `/doctor prompt-audit` on the touched scope. (Harness²; Claude Code docs; Ratchet)
12. **Verify reachability.** A skill needs its trigger in the diff. A hook needs a test against
    commands that must still pass. The next retro checks the transcript for the Skill call, the
    hook firing or `InstructionsLoaded`. (Harness² "never loaded … changed nothing")
13. **Ledger fields: `cue`, `predicts`, `cue-arose`.** Score each entry hit, miss or not-arisen.
    Prune exercised pieces with no hit over 4–5 retros; keep pieces whose cue never arose.
    (RRSI pruner; Bugbot candidate → active → disabled)
14. **Probe only narrow, repo-replayable calls.** Use one pair and a blind judge. A coordination
    failure can't be replayed solo, so use the critic and the next run's event log instead.
    (Harness²; current `probe.md`)
15. **Single-agent mode is the same pipeline with n = 1.** Skip the cross-agent counts in steps
    1 and 4. Every finding is `seen 1×` unless the ledger shows it recurring.
16. **The human approves every applied change.** Unreviewed, self-written skills ≈ 0.
    (SkillsBench; Ratchet)

**What NOT to do.**
- Don't let one LLM pass assign blame across agents without a quoted step and a corroborating
  log event (Who&When: 14.2% step accuracy).
- Don't count n agents who read each other as n trials (`sw-prior`).
- Don't answer a coordination failure with a brief sentence when the CLI could refuse it or
  flag it (grite; CLAUDE.md is not enforcement).
- Don't write session facts (this file, this bug, this agent) into skills or memory (RRSI critic
  rules 1 and 5; Harness² memory rule).
- Don't add a skill without a trigger, or name a script that doesn't ship (Harness² rules 1 and 3).
- Don't count adoption as success: "Adoption alone never establishes that an edit helped".
- Don't add unbounded checks or retries, or hooks that can block valid completion (RRSI rule 6;
  Harness²).
- Don't bundle fixes into one change, which leaves later retros unable to attribute (RRSI
  bundling rule and budget).
- Don't prune what was never exercised (RRSI pruner).

## Unverified or not fetched

Flagged where they appear above: the OpenAI post (403); HarnessX (secondary sources only, so
omitted); AgentLocate and FALAT numbers; SkillsBench's self-generated figure; the Harness² "w/o
scoping" row; Meta-Team mechanisms and numbers; grite per-condition numbers; the Anthropic
post's date.

## Sources

- RRSI, arXiv 2609.24972: https://arxiv.org/abs/2609.24972 · https://arxiv.org/html/2609.24972v3 · code https://github.com/google-research/rrsi (`rrsi/critic.py`, `propose.py`, `selection.py`, `analyst.py`, `history.py`, `domains/workspace/SKILL.md`) · https://regularized-rsi.com/
- Harness², arXiv 2610.14224: https://arxiv.org/abs/2610.14224 · https://arxiv.org/html/2610.14224v1 · code https://github.com/google-research/harness2 (`harness2/core/prompts.py`)
- Rethinking the Evaluation of Harness Evolution, arXiv 2607.12227: https://arxiv.org/abs/2607.12227
- SkillEvoReg, arXiv 2609.30861: https://arxiv.org/abs/2609.30861 · https://arxiv.org/html/2609.30861v1
- Ratchet, arXiv 2605.22148: https://arxiv.org/abs/2605.22148
- SkillsBench, arXiv 2602.12670: https://arxiv.org/abs/2602.12670
- Meta-Harness, arXiv 2603.28052: https://arxiv.org/abs/2603.28052
- TTHE, arXiv 2607.08124: https://arxiv.org/abs/2607.08124
- Meta-Team, arXiv 2605.29790: https://arxiv.org/abs/2605.29790
- Who&When, arXiv 2505.00212: https://arxiv.org/abs/2505.00212
- BLADE, arXiv 2610.18780: https://arxiv.org/abs/2610.18780
- Model or Harness?, arXiv 2607.28802: https://arxiv.org/abs/2607.28802
- CooperBench, arXiv 2601.13295: https://arxiv.org/abs/2601.13295
- Before the Pull Request (grite), arXiv 2606.19616: https://arxiv.org/abs/2606.19616
- Cursor, Continually improving our agent harness (30 Apr 2026): https://cursor.com/blog/continually-improving-agent-harness
- Cursor, Bugbot learned rules (8 Apr 2026): https://cursor.com/blog/bugbot-learning
- Anthropic, Effective harnesses for long-running agents: https://www.anthropic.com/engineering/effective-harnesses-for-long-running-agents
- Claude Code docs, memory: https://code.claude.com/docs/en/memory
- OpenAI, Harness engineering (11 Feb 2026; 403): https://openai.com/index/harness-engineering/
- In-repo: `harness-retro/SKILL.md`, `harness-retro/probe.md`, `swarm/DESIGN.md`, `swarm/research/sw-prior.md`, `swarm/research/sw-pitfalls.md`
