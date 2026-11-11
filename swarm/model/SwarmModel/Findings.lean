import SwarmModel.Comms

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

-- #25, S3 (board #26). covers takes `m/?` as a glob and as a directory, so it covers `m/?/x`; overlaps leaves a
-- glob's directory form out, so agent 1's `swarm lock m/?/x` is granted: the edit hook gives both agents that file.
example : let c : Cfg := { patterns := ["m/?", "m/?/x"], lockForms := false }
    ((run c [.lock 0 0, .lock 1 1]).isSome && covers c "m/?/x" "m/?" && covers c "m/?/x" "m/?/x") = true := by decide
-- With the fix a glob is only a glob (`m/?/x` is not under `m/?`), and S3's `overlap` is exact (`Glob.overlaps_iff`).
-- Before, overlaps also left out the pattern as a literal path and took `[!]a]` as the class `[!]` then `a]`
-- (covers: one character, not `]` or `a`): `[!]a]` and `b` share the file `b`, and both are granted.
example : let c : Cfg := { patterns := ["[!]a]", "b"], lockForms := false }
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
example : let c : Cfg := { patterns := ["m/?", "m/?/x"] }
    ((run c [.lock 0 0, .lock 1 1]).isSome && covers c "m/?/x" "m/?") = false := by decide
example : let c : Cfg := { patterns := ["[!]a]", "b"] }
    (run c [.lock 0 0, .lock 1 1]).isSome = false := by decide
-- #25's other half: overlaps over-approximated, refusing locks that share no file. A `?` met any class, even an
-- empty one (`[z-a]`), two classes always met, and a `*` met an empty class.
example : Glob.overlaps false "?".toList "[z-a]".toList = true := by decide
example : Glob.overlaps false "[a]".toList "[b]".toList = true := by decide
example : Glob.overlaps false "*c".toList "[z-a][c]".toList = true := by decide
example : Glob.overlaps true "?".toList "[z-a]".toList = false := by decide +kernel
example : Glob.overlaps true "[a]".toList "[b]".toList = false := by decide +kernel
example : Glob.overlaps true "*c".toList "[z-a][c]".toList = false := by decide +kernel

-- #12, work loss. Agent 0 owns two worktrees; the one wt_map picks (agent.wt: it edited there last) is landed, the
-- other has an uncommitted file. Before PR #123 lifecycle looks only at the first, so it ends the agent mid-task.
/-- some ended agent owns a worktree with work not on main -/
def endedWithWork (s : State) : Bool := (List.range s.ag.length).any fun a =>
  (s.agt a).st == .ended && (s.agt a).own.any fun (w, _) => owns s a w && !s.git.landed w
def twoWts : List Action := [.git 0 (.add 0), .git 0 (.edit 0), .git 0 (.add 1), .git 0 (.edit 1), .git 0 (.edit 0),
  .git 0 (.commit 0), .git 0 (.land 0 0), .stop 0 false, .age 0, .tick]
example : violates { nwts := 2, allWts := false } twoWts (!endedWithWork ·) = true := by decide
example : violates { nwts := 2 } twoWts (!endedWithWork ·) = false := by decide
-- a landed worktree does not keep the agent, and end_agent removes it and deletes its branch
example : (run { nwts := 1 } [.git 0 (.add 0), .git 0 (.edit 0), .git 0 (.commit 0), .git 0 (.land 0 0), .stop 0 false, .age 0,
    .tick]).any (fun s => (s.agt 0).st == .ended && !(s.git.wt 0).on && (s.git.tip 1).isNone) = true := by decide

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
set_option maxHeartbeats 400000 in
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
def keptByWt (s : State) : Bool := (s.agt 0).st == .idle && (s.agt 0).own.any fun (w, _) => owns s 0 w && !s.git.landed w
def unclean : List Action := [.git 0 (.add 0), .git 0 (.edit 0), .stop 0 false, .age 0, .stale 0]
example : stuckWith { nwts := 1, uncleanNudge := false } unclean keptByWt = true := by decide
example : stuckWith { nwts := 1 } unclean keptByWt = false := by decide
-- one nudge per idle stretch: a second is refused until the agent has woken and stopped again
example : (run { nwts := 1 } (unclean ++ [.nudge 0])).bind (step { nwts := 1 } · (.nudge 0)) = none := by decide
example : (run { nwts := 1 } (unclean ++ [.nudge 0, .wake 0, .stop 0 false, .age 0, .stale 0, .nudge 0])).isSome = true := by decide


-- ---------- #16, L1 for the pool: a lasso (board #141) ----------
/-- the states a run visits from `s` on, `s` first -/
def walk (c : Cfg) : State → List Action → Option (List State)
  | s, [] => some [s]
  | s, a :: as => (step c s a).bind fun s' => (walk c s' as).map (s :: ·)
/-- from the start `pre` leads to, `k` periods of `cyc` keep a startable task and a free slot (`idleSlot`) in every state,
and every fair action enabled in any of those states is in `cyc`: repeated forever the run is fair (strong fairness of
each action that is enabled infinitely often), and `idleSlot` holds forever -/
def lassoP (c : Cfg) (p : State → Bool) (pre cyc : List Action) (k : Nat) : Bool :=
  ((run c pre).bind fun s0 => walk c s0 (List.replicate k cyc).flatten).any fun ss =>
    ss.all fun s => p s && (fair c s).all fun f => (step c s f).isNone || cyc.contains f
def lassoOk (c : Cfg) (pre cyc : List Action) (k : Nat) : Bool := lassoP c (idleSlot c) pre cyc k
/-- one more period changes only the log, the cursor, what was shown and where each inbox starts: the state at the end of
period `k + 1` is the state at the end of period `k` with those four replaced, and the log is longer by `d` messages -/
def periodicD (c : Cfg) (d : Nat) (pre cyc : List Action) (k : Nat) : Bool :=
  match run c (pre ++ (List.replicate k cyc).flatten), run c (pre ++ (List.replicate (k + 1) cyc).flatten) with
  | some a, some b => decide ({ b with log := a.log, cursor := a.cursor, seen := a.seen, start := a.start } = a) && decide (b.log.length = a.log.length + d)
  | _, _ => false
def periodic (c : Cfg) (pre cyc : List Action) (k : Nat) : Bool := periodicD c 2 pre cyc k

-- Two tasks, two agent slots, agent 1 gone (so a slot is free). Agent 0 takes #1, stops holding it, its lease lapses, the
-- tick reaps it: agent 0 is idle with an unread `released`, so it is `reusable` and lifecycle does not spawn into the free
-- slot. It wakes, takes #2, and the same happens. The tick only runs after the lease lapsed, which fairness allows
-- (a tick while agent 0 holds a live lease would spawn onto the other task). The pool is never empty and the slot is
-- never filled, though each task is taken over and over: L1 holds for each task (`startable_leads_to`), not for the pool.
example : lassoOk { nagents := 2, roster := 2, ntasks := 2 } [.add [], .add [], .leave 1]
    [.claim 0 1, .stop 0 false, .age 0, .expire 1, .tick, .wake 0, .claim 0 2, .stop 0 false, .age 0, .expire 2, .tick, .wake 0]
    4 = true := by decide +kernel
example : periodic { nagents := 2, roster := 2, ntasks := 2 } [.add [], .add [], .leave 1]
    [.claim 0 1, .stop 0 false, .age 0, .expire 1, .tick, .wake 0, .claim 0 2, .stop 0 false, .age 0, .expire 2, .tick, .wake 0]
    2 = true := by decide +kernel

-- the check bites: without the tick in the period, the tick is enabled and never taken
example : lassoOk { nagents := 2, roster := 2, ntasks := 2 } [.add [], .add [], .leave 1]
    [.claim 0 1, .stop 0 false, .age 0, .expire 1, .wake 0, .claim 0 2, .stop 0 false, .age 0, .expire 2, .wake 0]
    4 = false := by decide +kernel

-- ---------- #17, L3: a spawned agent reaped before its first turn (board #142) ----------
-- Two slots, one task. Agent 0 takes #1, blocks it and goes idle with a big context, the answer is a DM it never reads
-- (it is cold). Reap reopens #1 and the tick ends agent 0 and spawns a new agent into its slot for #1: that agent
-- holds #1 with the answer still unread (the answer is stored on the task, but only `boot`, the spawned agent's first
-- turn, reads it). Before it boots, its lease lapses and the next tick reaps it, and spawns agent 1's slot for #1. Agent
-- 0 now boots (nothing to read: it holds nothing), goes idle big, and the same happens the other way round. Every fair
-- action that is enabled anywhere in the period is in the period (`boot` and `age` included), and #1 is never open at a
-- state of the run, so no `claim` is ever enabled: a fair run in which the answer is never read.
-- The model has no time between a lease and a boot; the Lua gives a spawned agent a fresh lease that is long next to a
-- boot, so this needs a hung launch each time. L3 holds only up to the first turn of a spawned agent; `bootFirst` (a boot beats a lease) is what closes it (`booting_reads`).
def cfg17 : Cfg := { nagents := 2, roster := 2, ntasks := 1, bootFirst := false }
def pre17 : List Action := [.add [], .claim 0 1, .block 0 1, .stop 0 true, .unblock 1, .age 0, .cool 0, .stop 1 true, .expire 1, .tick]
def cyc17 : List Action := [.age 1, .expire 1, .tick, .boot 0, .stop 0 true, .age 0, .expire 1, .tick, .boot 1, .stop 1 true]
example : lassoP cfg17 (!answered · 1) pre17 cyc17 4 = true := by decide +kernel
example : periodicD cfg17 2 pre17 cyc17 2 = true := by decide +kernel
-- the answer is read by the first turn: let the period's agent boot before its lease lapses
example : lassoP cfg17 (!answered · 1) pre17 [.boot 0] 1 = false := by decide +kernel
-- a boot beats a lease: with `bootFirst` the new agent's lease can't lapse, so the cycle's second `expire` is not enabled
example : run { cfg17 with bootFirst := true } (pre17 ++ [.age 1, .expire 1, .tick, .boot 0, .stop 0 true, .age 0, .expire 1]) = none := by decide +kernel

-- ---------- workspaces: W1-W4 on the current Cfg (sw-bases, board #2) ----------
/-- the tick from the run's end breaks W1: it is enabled, and removes a worktree or deletes a branch W1 forbids -/
def w1Breaks (c : Cfg) (acts : List Action) : Bool :=
  (run c acts).any fun s => (step c s .tick).isSome && !gcOk c s (tickOf c s).git

-- #18, W1. A protected ref deleted. Agent 0 lands its commit on `formal` (base 1) and on main, then checks `formal` out in
-- its worktree and leaves. 30 min on, the sweep finds the worktree clean, unused and on main, removes it and runs
-- `git branch -D formal`: the swarm's base is gone (the replay's script-sweep run shows the Lua doing it).
def cfg18 : Cfg := { nwts := 1, nbases := 2 }
def pre18 : List Action := [.git 0 (.add 0), .git 0 (.edit 0), .git 0 (.commit 0), .git 0 (.land 0 1), .git 0 (.land 0 0),
  .git 0 (.checkout 0 1), .world 0 .age, .leave 0]
example : w1Breaks cfg18 pre18 = true := by decide
example : (run cfg18 (pre18 ++ [.tick])).any (fun s => (s.git.tip 1).isNone) = true := by decide
-- #18b, W1. A worktree removed with a process inside: end_agent looks at no process. Agent 0's work is on main, a
-- process sits in its worktree (a dev server, a shell), it stops and ages: the tick ends it and removes the worktree.
def cfg18b : Cfg := { nwts := 1 }
def pre18b : List Action := [.git 0 (.add 0), .git 0 (.edit 0), .git 0 (.commit 0), .git 0 (.land 0 0), .world 0 (.proc true),
  .stop 0 false, .age 0]
example : w1Breaks cfg18b pre18b = true := by decide
-- with `splitGC` neither: the sweep keeps `formal` (removes the worktree only), end_agent removes nothing
example : w1Breaks { cfg18 with splitGC := true } pre18 = false := by decide
example : (run { cfg18 with splitGC := true } (pre18 ++ [.tick])).any
    (fun s => !(s.git.wt 0).on && (s.git.tip 1).isSome) = true := by decide
example : w1Breaks { cfg18b with splitGC := true } pre18b = false := by decide

-- #19, W2 (fails by design today). The same run with no process: the worktree was touched within 30 min, so the sweep
-- keeps it, but the tick that ends agent 0 removes it and deletes its branch. With `splitGC` the tick ends the agent
-- and leaves git alone.
def pre19 : List Action := [.git 0 (.add 0), .git 0 (.edit 0), .git 0 (.commit 0), .git 0 (.land 0 0), .stop 0 false, .age 0]
example : violates cfg18b pre19 (endKeepsGit cfg18b) = true := by decide
example : violates { cfg18b with splitGC := true } pre19 (endKeepsGit { cfg18b with splitGC := true }) = false := by decide
example : (run { cfg18b with splitGC := true } (pre19 ++ [.tick])).any
    (fun s => (s.agt 0).st == .ended && (s.git.wt 0).on) = true := by decide

-- #20, W3 with a base that isn't main (the notapki `formal` swarm). Agent 1 starts and ends a background job over and
-- over, so the run goes on; every other fair action is off (`loopOk`), so the run is fair.
/-- in s, every enabled fair action is one of `xs` -/
def onlyFair (c : Cfg) (s : State) (xs : List Action) : Bool := (fair c s).all fun f => (step c s f).isNone || xs.contains f
/-- a two-state loop after `pre`: `x` then `y` come back to the start, and no other fair action is enabled on the way -/
def loopOk (c : Cfg) (pre : List Action) (x y : Action) (p : State → Bool) : Bool :=
  (run c pre).any fun s => (step c s x).any fun s' => step c s' y == some s && p s && p s'
    && onlyFair c s [x, y] && onlyFair c s' [x, y]
def cfg20 : Cfg := { nwts := 1, nbases := 2 }
-- The workspace half. Agent 0 lands on `formal` and leaves; the worktree is clean, unused, untouched 30 min, its HEAD on
-- a protected ref, but not on main, so the sweep never removes it.
def pre20 : List Action := [.git 0 (.add 0), .git 0 (.edit 0), .git 0 (.commit 0), .git 0 (.land 0 1), .world 0 .age, .leave 0]
example : loopOk cfg20 pre20 (.bgStart 1) (.bgEnd 1) (orphan cfg20 · 0) = true := by decide
-- The agent half. Agent 0 claims #1, whose base is `formal`, lands it there, marks it done, stops and ages: idle, free,
-- its worktree clean and on its task's base. Lifecycle's landed check asks main, so it is never ended (and a waiter it
-- has is woken only by the unclean nudge, if it goes stale: then it is nudged once per idle stretch, forever).
def cfg20b : Cfg := { nwts := 1, nbases := 2, taskBase := [0, 1] }
def pre20b : List Action := [.add [], .claim 0 1, .git 0 (.add 0), .git 0 (.edit 0), .git 0 (.commit 0), .git 0 (.land 0 1),
  .done 0 1 true, .stop 0 false, .age 0]
example : loopOk cfg20b pre20b (.bgStart 1) (.bgEnd 1) (doneOnBase cfg20b · 0) = true := by decide
-- with `perTaskBase` the tick removes the worktree, and ends the agent
-- (the sweep protects a base some task names: #1 is on `formal`; the agent's task is #1)
example : (run { cfg20 with perTaskBase := true, taskBase := [0, 1] } ([.add []] ++ pre20 ++ [.tick])).any (fun s => !(s.git.wt 0).on) = true := by decide
example : (run { cfg20b with perTaskBase := true } (pre20b ++ [.tick])).any (fun s => (s.agt 0).st == .ended) = true := by decide

-- #B1 (finding, board #3), B1 (sw-bases, board #3). Work is landed on the base of the task it was done for. Agent 0's task #1 is on `formal`;
-- it lands on main, not on `formal`, marks #1 done and goes idle. Lifecycle's check asks main only, so it ends the agent:
-- its work never reached `formal`. With `perTaskBase` it asks `formal`, and keeps the agent.
def cfgB1 : Cfg := { nwts := 1, nbases := 2, taskBase := [0, 1] }
def preB1 : List Action := [.add [], .claim 0 1, .git 0 (.add 0), .git 0 (.edit 0), .git 0 (.commit 0), .git 0 (.land 0 0),
  .done 0 1 true, .stop 0 false, .age 0]
example : (run cfgB1 (preB1 ++ [.tick])).any (fun s => (s.agt 0).st == .ended) = true := by decide
example : (run { cfgB1 with perTaskBase := true } (preB1 ++ [.tick])).any (fun s => (s.agt 0).st == .ended) = false := by decide

-- #21, W4. Agent 0 checks out `formal` in its worktree; agent 1's commit can no longer land on it (`git push . HEAD:formal`
-- is refused while a worktree has it checked out). With `recordedWorkspaces` the checkout is refused.
def cfg21 : Cfg := { nwts := 2, nbases := 2 }
def pre21 : List Action := [.git 0 (.add 0), .git 0 (.checkout 0 1)]
example : violates cfg21 pre21 (noBaseOut cfg21) = true := by decide
example : run cfg21 (pre21 ++ [.git 1 (.add 1), .git 1 (.edit 1), .git 1 (.commit 1), .git 1 (.land 1 1)]) = none := by decide
example : run cfg21 [.git 1 (.add 1), .git 1 (.edit 1), .git 1 (.commit 1), .git 1 (.land 1 1)] ≠ none := by decide
example : run { cfg21 with recordedWorkspaces := true } pre21 = none := by decide

-- ---------- the communicator: C1 on the current CCfg (board #8) ----------
-- #22, C1. One terminal is the communicator of two swarms (2026-11-10: sk-comms and fm-comms both on t87, in the notapki
-- space). Terminal 0 opens in space 1, swarm 1's home; fm-comms joins swarm 1 from it, then sk-comms joins swarm 0 from
-- the same terminal: bind looks only at swarm 0's own row, so nothing refuses. The session is sk-comms now: its
-- `swarm wait` reads swarm 0's db, and swarm 1's notices to fm-comms are stored and read by no one. Swarm 0's
-- communicator sits outside its space as well.
def cfg22 : CCfg := {}
def pre22 : List CAction := [.open 1, .join 1 0 false, .join 0 0 false, .watchd 1 0]
example : c1Breaks cfg22 pre22 1 = true := by decide
example : c1Breaks cfg22 (pre22 ++ [.watchd 0 0]) 0 = true := by decide
-- with `ensureComms` the second join is refused (another swarm's communicator, outside swarm 0's space), with
-- `--takeover` too (the space); swarm 1 alone is fine
example : crun { cfg22 with ensureComms := true } pre22 = none := by decide
example : crun { cfg22 with ensureComms := true } [.open 1, .join 1 0 false, .join 0 0 true] = none := by decide
example : c1Breaks { cfg22 with ensureComms := true } [.open 1, .join 1 0 false, .watchd 1 0] 1 = false := by decide

-- #23, C1. The communicator's terminal dies and the swarm runs on. Watchd runs from another terminal of the swarm's
-- space; agent 0 blocks #1 and the communicator's terminal dies. The tick reaps the communicator's row and nothing binds
-- a new one (`tick_binds_none`: no tick ever does), so the notice that #1 is blocked goes to a name no one reads.
def cfg23 : CCfg := { nswarms := 1, home := [0] }
def pre23 : List CAction := [.open 0, .join 0 0 false, .open 0, .watchd 0 1, .sw 0 (.add []), .sw 0 (.claim 0 1),
  .sw 0 (.block 0 1), .die 0]
example : c1Breaks cfg23 pre23 0 = true := by decide
example : (crun cfg23 (pre23 ++ [.tick 0, .tick 0])).any
    (fun w => w.cm 0 == none && ((w.st 0).tk 1).st == .blocked) = true := by decide
-- with `ensureComms` the tick launches a communicator in the swarm's space
example : c1Breaks { cfg23 with ensureComms := true } pre23 0 = false := by decide
-- but between the death and the tick no fix helps: C1 of every reachable state is false
example : (crun { cfg23 with ensureComms := true } pre23).any (fun w => watchdUp w 0 && !c1 { cfg23 with ensureComms := true } w 0)
    = true := by decide

-- #24, C1. Watchd started from a terminal in another space spawns there. The communicator is in the swarm's space,
-- watchd runs from terminal 1 in space 1; agent 0 leaves and #1 is added: the tick spawns for #1, and launch.sh opens the
-- tab in the space of watchd's terminal.
def cfg24 : CCfg := { sw := { nagents := 1, roster := 1 }, nswarms := 1, home := [0] }
def pre24 : List CAction := [.open 0, .join 0 0 false, .open 1, .watchd 0 1, .sw 0 (.leave 0), .sw 0 (.add [])]
example : c1Breaks cfg24 pre24 0 = true := by decide
example : (crun cfg24 (pre24 ++ [.tick 0])).any (fun w => ((w.st 0).agt 0).boot && w.spaceOf 0 0 == 1) = true := by decide
-- with `ensureComms` the spawn lands in the swarm's space
example : c1Breaks { cfg24 with ensureComms := true } pre24 0 = false := by decide

/-- #22: one terminal is the communicator of two swarms -/
theorem not_C1_shared : ¬ C1 cfg22 := not_C1_of (by decide : c1Breaks cfg22 pre22 1 = true)
/-- #23: the communicator's terminal dies and no one replaces it -/
theorem not_C1_dead : ¬ C1 cfg23 := not_C1_of (by decide : c1Breaks cfg23 pre23 0 = true)
/-- #24: watchd's spawns land in its own terminal's space -/
theorem not_C1_space : ¬ C1 cfg24 := not_C1_of (by decide : c1Breaks cfg24 pre24 0 = true)
/-- C1 of every reachable state fails with the fix on: a terminal dies before watchd's next tick -/
theorem not_C1all_fixed : ¬ C1all { cfg23 with ensureComms := true } :=
  not_C1all_of (acts := pre23) (i := 0) (by decide)
/-- #22 to #24 with `ensureComms` (board #10): C1 holds in each one's world, so no run of it breaks C1 -/
example : C1 { cfg22 with ensureComms := true } ∧ C1 { cfg23 with ensureComms := true } ∧
    C1 { cfg24 with ensureComms := true } := ⟨C1_of _ rfl, C1_of _ rfl, C1_of _ rfl⟩

end Swarm
