# How to write the spec a reviewer reads

A reviewer of a change reads its intent and the spec. They do not read the code or the proofs. The spec is the theorem
statements of `SwarmModel/Contract.lean` and every definition those statements mention. These rules are for that
text. Proof files and the model's own functions are outside them.

The test for a statement: someone who knows what the swarm does, and reads Lean's `∀`, `∃`, `→`, `∧`, `∨`, `¬`,
can say it aloud in one sentence, and the sentence is the docstring.

## Rules

1. **State a property as a `Prop` with quantifiers.** No `List.all`, `any`, `&&`, `||`, `!`, `==` or `decide` in a
   statement or in a definition it mentions.

   ```lean
   -- before: the reader runs two loops and a De Morgan in their head
   oneWorker s = true
   -- after
   ∀ a b t, WorksOn s a t → WorksOn s b t → a = b
   ```

   A Bool field of the state (`(s.agt a).bg = true`) or a one-line named query of `Model.lean` (`(s.agt a).live =
   true`, `owns s a w = true`) may appear as `= true` or `= false`: giving each a Prop twin would write the model
   twice. The query's definition is then part of what the reviewer reads, so use few.

2. **Name the middle concepts.** When a statement needs a phrase to be said aloud ("works on", "holds work",
   "mid-tick"), that phrase is a definition with a docstring: `WorksOn s a t`, `HoldsWork c s a`, `MidTick w i p`.
   A definition is one idea and at most about five lines. Props are `UpperCamelCase`, the model's functions and Bool
   checkers stay `lowerCamelCase`.

3. **Use words for names.**

   | | no | yes |
   |---|---|---|
   | theorem | `s1_oneWorker`, `l4_deadLive` | `one_worker_per_task`, `gone_terminal_row_is_ended` |
   | hypothesis | `h`, `hfix`, `hR`, `hw` | `reachable`, `fixes`, `watchd_runs`, `fair` |
   | bound variable | `o`, `h` for a terminal | `owner`, `terminal` (`s`, `a`, `t`, `c`, `w`, `n` keep their meaning: state, agent, task, config, worktree or world, step) |

   The property's id (S1, N1, L4) goes in the docstring, where the README's tables find it. It is not the name.

4. **A property with several parts is a structure with named fields**, each field a part with its own docstring
   (`NoWorkLost.tick_keeps_agent_holding_work`), not a chain of `∧` read by position.

5. **Bundle the switches about our code. Never bundle an assumption about anything else.**
   - A property's fixes (the `Cfg` switches that are our code before and after a fix) go in one structure named after
     the property, each field named for what the fixed code does and typed by the switch: `S1Fixes c`, with
     `reap_takes_from_idle_only : c.release = .idle`. The theorem takes `(fixes : S1Fixes c)`.
   - An assumption about an outside tool (`Env.lean`: git, hc, gh, sqlite, the kernel) stays its own named hypothesis
     in the statement: `(hc_ls_lists_the_live : HcLsLive t)`. This is board #68's rule; a bundle hides which
     assumption a result rests on, and `Audit.lean` prints them one by one.
   - A condition that is neither (watchd runs, `hc ls` answers, a run is fair, the model's mode `racy`) is also its
     own named hypothesis. The reader must see each one to know when the guarantee applies.

6. **Keep every Bool checker and tie it to its Prop with an iff.** The replay and the counterexamples run the
   checkers (`oneWorker`, `holdsWork`, `deadLive`); they can't run a `Prop`. For each, `SwarmModel/Checkers.lean`
   proves `checker … = true ↔ <the property written out with ∀ ∃ ∧ ∨>`, and `Contract.lean` cites it under the
   readable name: `theorem oneWorker_iff (s) : oneWorker s = true ↔ OneWorkerPerTask s := oneWorker_spec s`. That line
   compiles only while the named definitions unfold to exactly what `Checkers.lean` proves. A theorem that was stated
   with the checker is restated with the Prop and proved from the old one through the iff, so the old statement still
   follows and nothing is weakened.

7. **`Contract.lean` reads top to bottom.** Before each statement: the definitions it needs, then their iff lemmas,
   then the fixes structure. A definition used by several statements is given once, before the first. Every proof in
   the file is a reference to a theorem elsewhere, on one line where it fits; anything that takes tactics goes in the
   module that owns the subject or in `Checkers.lean`.

8. **A definition that must live elsewhere is shown, not paraphrased.** `Audit.lean` requires the environment
   hypotheses to be in `Env.lean`. Show one where it is used with a checked line:

   ```lean
   example (t : Tools) : HcLsLive t = ∀ w terminal, t.hcLs w terminal = t.termLive w terminal := rfl
   ```

   A docstring that repeats a definition in English drifts; this line fails to build when the definition changes.

9. **The docstring says the guarantee in one sentence, then what it rests on.** `Env:` lists the environment
   hypotheses, or `none`. Fixes are no longer listed in prose: the fixes structure is the list. Say which
   counterexample shows a hypothesis is needed (`not_S1_humanRelease`).

10. **Never weaken to make it readable.** If the readable form is not equivalent to the old one, the iff won't prove,
    and that is the signal to stop and fix the definition, not the iff.

## What stays as it is

- Temporal statements keep their explicit `∃ m, n ≤ m ∧ …` until three statements share a shape worth naming.
- `Reachable`, `step`, `Run`, `Run.Fair`, `tickOf` and the state's fields are the model. They are not restated; the
  README's *What a reviewer reads and trusts* lists them as required reading.
- Proofs, invariants and helper lemmas in the other modules keep their short names.

## Converting a statement

1. Write the sentence. Underline each phrase that is not a field of the state: those are the definitions (rule 2).
2. Write the Props. For each Bool checker they replace, add the `_spec` lemma to `Checkers.lean` and the `_iff`
   line to `Contract.lean`.
3. Sort the hypotheses: fixes into the structure, everything else named and separate (rule 5).
4. Restate the theorem, prove it from the old theorem through the iff, rename it (rule 3), and update the names in
   `README.md` and `example/Client.lean`.
5. `swarm/model/check.sh`.
