import SwarmModel.Model

/-! The counterexamples the Quint model found, as runs of this model with the fix's switch off: each `example`
is checked by evaluating the run. README.md has the table; the theorems that a safety property holds with the fix
on are in Basic, Locks, Inbox and Workers. A liveness counterexample is a run to a state where the property fails
and no fair action is enabled. -/

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

-- #12, work loss. Agent 0 owns two worktrees; the one wt_map picks is landed, the other has work not on main. Before
-- PR #123 lifecycle looks only at the first, so it ends the agent mid-task.
def endedWithWork (s : State) : Bool := (List.range s.ag.length).any fun a =>
  (s.agt a).st == .ended && ((s.agt a).wt1 || (s.agt a).wt2)
example : violates { allWts := false } [.dirty 0 true true, .stop 0 false, .age 0, .tick] (!endedWithWork ·) = true := by decide
example : violates {} [.dirty 0 true true, .stop 0 false, .age 0, .tick] (!endedWithWork ·) = false := by decide
-- a landed worktree does not keep the agent
example : (run {} [.dirty 0 true true, .dirty 0 true false, .stop 0 false, .age 0, .tick]).any
    (fun s => (s.agt 0).st == .ended) = true := by decide

-- ---------- liveness ----------
/-- The actions fairness makes happen if they stay enabled: watchd ticks (and so the reap of a row whose terminal `hc ls` no longer lists), leases lapse, idle agents age, a spawned
agent boots, a waiter with a message it wakes on wakes, an hc prompt is answered, a working agent reads its
messages and takes work, a background job ends, and the second half of a split command follows the first. -/
def fair (c : Cfg) (s : State) : List Action :=
  .tick :: c.tasks.map .expire ++ c.agents.map .reapGone ++ (c.agents.filter fun a => !(s.agt a).dead).flatMap fun a =>
    [.age a, .bgEnd a, .nudge a, .boot a, .wake a, .wakeRead a, .wakeWrite a, .claimWrite a, .hcClear a, .readAll a]
      ++ c.tasks.map (.claim a) ++ c.tasks.map (.claimRead a)
/-- no fair action is enabled: a fair run may stay in this state forever. A dead agent's own actions don't count:
it does nothing more. -/
def stuck (c : Cfg) (s : State) : Bool := (fair c s).all fun act => (step c s act).isNone
/-- does the run end in a state that is stuck with `p` true? Then `p` is true forever on a fair run. -/
def stuckWith (c : Cfg) (acts : List Action) (p : State → Bool) : Bool := (run c acts).any fun s => stuck c s && p s
/-- L4: a row that reads as live whose terminal is gone -/
def deadLive (s : State) (a : Nat) : Bool := (s.agt a).live && (s.agt a).dead
/-- what L1 forbids forever: a startable task and a free slot -/
def idleSlot (c : Cfg) (s : State) : Bool := slotFree c s && !(pool c s).isEmpty

-- #1, L2. 624cf79 keeps a lapsed claim while its owner is live: agent 0 goes idle holding #1 and nothing wakes it.
example : stuckWith { nagents := 1, roster := 1, release := .ended }
    [.add [], .claim 0 1, .stop 0 false, .expire 1, .age 0] (idleClaim · 0 1) = true := by decide

-- #3, L3. The unblock answer is only a DM to the owner, who is idle with a big context and cold, so a message
-- that isn't urgent doesn't wake it. Reap reopens #1, the owner is ended, a new agent is spawned for #1: it never
-- gets the answer.
example : stuckWith { nagents := 1, roster := 1, answerOnTask := false }
    [.add [], .claim 0 1, .block 0 1, .stop 0 true, .age 0, .cool 0, .unblock 1, .expire 1, .tick, .boot 0, .expire 1]
    (!answered · 1) = true := by decide

-- #8, L1 and L3. Agent 0 was told of #1 and went idle again without it (agent 1 had it by then). Agent 1 leaves:
-- #1 is open with its answer, a slot is free, and lifecycle keeps agent 0 reusable instead of spawning.
example : let c : Cfg := { passedOver := false }
    stuckWith c [.stop 0 false, .age 0, .add [], .tick, .wake 0, .claim 1 1, .block 1 1, .unblock 1, .stop 0 false,
      .age 0, .leave 1] (fun s => idleSlot c s && !answered s 1) = true := by decide

-- #9, L1 and L3. The same with agent 0's waiter gone: it never reads the digest, so PR #116 doesn't end it.
example : let c : Cfg := { waiterAlive := false }
    stuckWith c [.add [], .claim 1 1, .block 1 1, .unblock 1, .stop 0 false, .age 0, .waiterGone 0, .leave 1, .tick]
      (fun s => idleSlot c s && !answered s 1) = true := by decide

-- #14, L4 (a dead agent is ended). Agent 0 holds #1 and its terminal dies with no `swarm leave`. With no watchd
-- (`watchd := false`) nothing ever ends the row: it reads as live (`swarm who` and `swarm post` show it gone, from
-- `hc ls` at read time, but the row stays), and its claim stays with it. Agent 1's message to it is stored, unread.
example : stuckWith { watchd := false } [.add [], .claim 0 1, .die 0, .postTo 1 0 false, .expire 1] (deadLive · 0) = true := by decide
example : stuckWith { watchd := false } [.add [], .claim 0 1, .die 0, .postTo 1 0 false, .expire 1]
    (fun s => ownsClaimed s 0 1 && !(unread s 0).isEmpty) = true := by decide

-- #15, L4. watchd runs but can't tell: `hc ls` doesn't answer (`hcSees := false`: `live_addrs` is nil, no row is judged
-- dead), or the row has no hc address (`unbound`, e.g. a communicator that joined from outside hc). The dead agent was
-- working, so reap keeps its claim past the lease (`keeps`: the owner isn't idle) and the task stays claimed forever.
example : stuckWith { hcSees := false } [.add [], .claim 0 1, .die 0, .expire 1] (fun s => deadLive s 0 && ownsClaimed s 0 1) = true := by decide
example : stuckWith { unbound := [0] } [.add [], .claim 0 1, .die 0, .expire 1] (fun s => deadLive s 0 && ownsClaimed s 0 1) = true := by decide

-- The same runs with the fix on: none ends stuck.
example : stuckWith {} [.add [], .claim 0 1, .die 0, .postTo 1 0 false, .expire 1] (deadLive · 0) = false := by decide
example : stuckWith {} [.add [], .claim 0 1, .die 0, .expire 1] (deadLive · 0) = false := by decide
example : stuckWith { nagents := 1, roster := 1 }
    [.add [], .claim 0 1, .stop 0 false, .expire 1, .age 0] (idleClaim · 0 1) = false := by decide
example : stuckWith { nagents := 1, roster := 1 }
    [.add [], .claim 0 1, .block 0 1, .stop 0 true, .age 0, .cool 0, .unblock 1, .expire 1, .tick, .boot 0, .expire 1]
    (!answered · 1) = false := by decide
example : stuckWith {} [.stop 0 false, .age 0, .add [], .tick, .wake 0, .claim 1 1, .block 1 1, .unblock 1, .stop 0 false,
    .age 0, .leave 1] (fun s => idleSlot {} s && !answered s 1) = false := by decide
example : stuckWith {} [.add [], .claim 1 1, .block 1 1, .unblock 1, .stop 0 false, .age 0, .waiterGone 0, .leave 1, .tick]
    (fun s => idleSlot {} s && !answered s 1) = false := by decide

-- ---------- the idle owner with a background job (board #115, found on #107) ----------
/-- task 1 is held by agent 1 while agent 0, who had it, is live with its background job running -/
def takenFromJob (s : State) : Bool := ((s.tk 1).owner == some 1 && (s.agt 0).bg && (s.agt 0).live)

-- #10, S1-like (work lost). Agent 0 claims #1, starts a long job and stops; the lease lapses; with `bgKeeps` off
-- reap reopens #1 (its owner is idle) and, agent 1 having left, watchd spawns agent 1 onto it while 0's job runs.
example : violates { bgKeeps := false } [.add [], .claim 0 1, .bgStart 0, .stop 0 false, .expire 1, .leave 1, .tick]
    (!takenFromJob ·) = true := by decide

-- #11. Reap took #1 from agent 0, whose context is big (the 350k fence): with `retake` off `task claim` refuses it
-- the task it held, so the run cannot continue; with it on the claim goes through.
example : (run { retake := false } [.add [], .claim 0 1, .stop 0 true, .expire 1, .tick, .prompt 0, .claim 0 1]).isNone = true := by decide

-- The same runs with the fix on.
example : violates {} [.add [], .claim 0 1, .bgStart 0, .stop 0 false, .expire 1, .leave 1, .tick] (!takenFromJob ·) = false := by decide
example : (run {} [.add [], .claim 0 1, .stop 0 true, .expire 1, .tick, .prompt 0, .claim 0 1]).isSome = true := by decide
-- #13, L5. Agent 0 is idle 30 min, kept only by an unclean worktree. Before PR #122 nothing is enabled, forever and
-- silently; with it, `nudge` is (the urgent message wakes the waiter), once per idle stretch.
def keptByWt (s : State) : Bool := (s.agt 0).st == .idle && ((s.agt 0).wt1 || (s.agt 0).wt2)
example : stuckWith { uncleanNudge := false } [.dirty 0 false true, .stop 0 false, .age 0, .stale 0] keptByWt = true := by decide
example : stuckWith {} [.dirty 0 false true, .stop 0 false, .age 0, .stale 0] keptByWt = false := by decide
-- one nudge per idle stretch: a second is refused until the agent has woken and stopped again
example : (run {} [.dirty 0 false true, .stop 0 false, .age 0, .stale 0, .nudge 0]).bind (step {} · (.nudge 0)) = none := by decide
example : (run {} [.dirty 0 false true, .stop 0 false, .age 0, .stale 0, .nudge 0, .wake 0, .stop 0 false, .age 0, .stale 0,
    .nudge 0]).isSome = true := by decide

end Swarm
