import SwarmModel.Model

/-! The counterexamples the Quint model found, as runs of this model with the fix's switch off: each `example`
is checked by evaluating the run. README.md has the table; the theorems that the property holds with the fix on
are in the Safety files. -/

namespace Swarm

/-- does the run end in a state where `p` fails? -/
def violates (c : Cfg) (acts : List Action) (p : State → Bool) : Bool := (run c acts).any (!p ·)

-- #2, S1. b04cf08 reopens a lapsed claim whenever the owner isn't working, including one at an hc permission
-- prompt: agent 1 claims #1 and stops at a prompt; the lease lapses, reap reopens #1, agent 0 claims it.
example : violates { release := .notWorking }
    [.add [], .claim 1 1, .hcPrompt 1, .unblock 1, .expire 1, .tick, .claim 0 1] oneWorker = true := by decide

-- #4, S2. `task claim` reads #2's dependencies, `task after` adds #1 (not done), the claim's write succeeds.
example : violates { ntasks := 2, racy := true, claimChecksDeps := false }
    [.add [], .add [], .claimRead 0 2, .after 2 [1], .claimWrite 0] noEarlyStart = true := by decide

-- #5, S5. `task done --evidence ""` is accepted.
example : violates { evidenceRequired := false } [.add [], .claim 0 1, .done 0 1 false] doneHasEvidence = true := by decide

-- #6, S3. `m/*.lua` and `m/a*` both match `m/a.lua`; neither covers the other as a path, so both are granted.
example : let c : Cfg := { patterns := ["m/*.lua", "m/a*", "m/"], lockOverlap := false }
    violates c [.lock 0 0, .lock 1 1] (locksDisjoint c) = true := by decide

-- #7, S4. The waiter reads agent 0's unread list, a hook delivers it and moves the cursor, the waiter writes its
-- cursor and shows the same message again.
example : violates { racy := true, deliverCas := false }
    [.stop 0 false, .postTo 1 0 false, .wakeRead 0, .prompt 0, .wakeWrite 0] inboxExact = true := by decide

-- The same runs with the fix on: none ends in a violation (the theorems say no run does).
example : violates {} [.add [], .claim 1 1, .hcPrompt 1, .unblock 1, .expire 1, .tick, .claim 0 1] oneWorker = false := by decide
example : violates { ntasks := 2, racy := true }
    [.add [], .add [], .claimRead 0 2, .after 2 [1], .claimWrite 0] noEarlyStart = false := by decide
example : violates {} [.add [], .claim 0 1, .done 0 1 false] doneHasEvidence = false := by decide
example : let c : Cfg := { patterns := ["m/*.lua", "m/a*", "m/"] }
    violates c [.lock 0 0, .lock 1 1] (locksDisjoint c) = false := by decide
example : violates { racy := true }
    [.stop 0 false, .postTo 1 0 false, .wakeRead 0, .prompt 0, .wakeWrite 0] inboxExact = false := by decide

end Swarm
