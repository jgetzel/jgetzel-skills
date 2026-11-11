import SwarmModel.Glob

/-! The coordination swarm/lua/swarm implements: the board, leases and watchd's reaping and auto-spawn, locks,
agents, and inboxes, as plain Lean: one `State`, one function per command or event (`none` is "not enabled"),
`step` over an `Action`, and `Reachable`. The proofs are in the other files (README.md says which); `Traces.lean`
writes random runs that `../lua/test/cli_model_spec.lua` replays through the CLI. README.md lists every
property as a sentence and says what is proved, replayed and not modelled.

Agents are slots `0, 1, ..`, tasks ids `1, 2, ..` (0 is "none"), lock patterns indexes into `Cfg.patterns`,
message ids positions in the log from 1. Any number of each. -/

namespace Swarm

/-- Which lapsed claims reap reopens: `ended` (624cf79), `notWorking` (b04cf08), `idle` (edffafc, now). -/
inductive Release where | ended | notWorking | idle
  deriving DecidableEq, Repr, Inhabited
inductive TSt where | absent | opn | claimed | blocked | done | dropped
  deriving DecidableEq, Repr, Inhabited
inductive ASt where | unborn | working | idle | blocked | ended
  deriving DecidableEq, Repr, Inhabited
inductive Kind where | dm | answer | released | digest | nudge
  deriving DecidableEq, Repr, Inhabited

/-- The instance: sizes, and one switch per fix, so the model is the code before and after it. The defaults
are main now. -/
structure Cfg where
  /-- agent slots; the first `roster` are live at the start, a spawn fills the first not live -/
  nagents : Nat := 2
  /-- also watchd's --max-agents: it refills the roster, never grows it -/
  roster : Nat := 2
  ntasks : Nat := 1
  /-- lock patterns agents may take -/
  patterns : List String := []
  release : Release := .idle
  /-- unblock --answer is stored on the task (PR #110) -/
  answerOnTask : Bool := true
  /-- claim, and the waiter's delivery, are a read then a write, as the Lua runs them -/
  racy : Bool := false
  /-- claim's write rechecks the deps (PR #112); before, only state='open' -/
  claimChecksDeps : Bool := true
  /-- task done refuses empty evidence (PR #113) -/
  evidenceRequired : Bool := true
  /-- swarm lock refuses any common file (PR #114); before, only one pattern covering the other -/
  lockOverlap : Bool := true
  /-- a glob is not also a directory, and `overlaps` is exact: every form of both patterns, `?` and classes by
  the bytes they match (board #26); before, `m/?` covered `m/?/x` but `swarm lock` let another agent lock it -/
  lockForms : Bool := true
  /-- a delivery moves the cursor only from where it read, else reads again (PR #115) -/
  deliverCas : Bool := true
  /-- lifecycle ends a reusable agent told of the whole pool, inbox read, idle again (PR #116) -/
  passedOver : Bool := true
  /-- lifecycle keeps an agent reusable only while its waiter is alive (PR #119) -/
  waiterAlive : Bool := true
  /-- reap keeps a lapsed claim whose idle owner has a live background job (PR #121) -/
  bgKeeps : Bool := true
  /-- `task claim` refuses an agent with a big context (the 350k fence), unless reap took this very task from it
  (PR #121); with `retake` off the fence has no exception -/
  retake : Bool := true
  /-- lifecycle keeps an agent while any worktree it owns is unlanded (PR #123); before, only the one wt_map picks -/
  allWts : Bool := true
  /-- watchd nudges an agent kept only by an unclean worktree, once per idle stretch (PR #122); before, silence -/
  uncleanNudge : Bool := true
  /-- watchd runs: false is the mode with none, where nothing ticks -/
  watchd : Bool := true
  /-- `hc ls` answers, so watchd can tell a terminal is gone (else `live_addrs` is nil and no row is judged dead) -/
  hcSees : Bool := true
  /-- slots whose row has no hc address (`agent.hc` null): `hc ls` can't show their terminal gone -/
  unbound : List Nat := []
  /-- a boot beats a lease: a spawned agent's lease does not lapse before its first turn. The Lua gives it a fresh 2 h
  lease and it boots in seconds; with this off the lease can lapse first, over and over (finding #17) -/
  bootFirst : Bool := true
  /-- git worktree slots agents may add (the main checkout is outside the model) -/
  nwts : Nat := 0
  /-- base branches: 0 is `main`, the one the Lua's landed checks use; the rest exist from the start (a swarm's own
  base, e.g. `formal`). Branch `nbases + w` is worktree w's own -/
  nbases : Nat := 1
  /-- sw-bases, board #3: the landed checks use per-task bases (`base_for`): lifecycle asks the bases of the tasks an agent
  owns (main if none), the sweep every base a task names and main -/
  perTaskBase : Bool := false
  /-- the base of task t (index t; main, 0, past the end): fixed when the task is added (`swarm task add --base`) -/
  taskBase : List Nat := []
  /-- sw-bases, board #4: ending an agent only kills its terminal; workspace GC alone removes worktrees, by reachability
  from a protected ref, and `branch -D` only of a branch that is no base and is reachable. Before, end_agent removes the
  ended agent's worktree (with no look at processes) and sweep deletes whatever branch was checked out but main -/
  splitGC : Bool := false
  /-- sw-bases, board #5: swarm creates and records each worktree, and an agent never checks out a base -/
  recordedWorkspaces : Bool := false
  deriving DecidableEq, Repr, Inhabited

structure Task where
  st : TSt
  owner : Option Nat
  deps : List Nat
  lease : Bool
  ev : Bool
  answer : Bool
  /-- blocked by an hc prompt, not by `task block` -/
  hcq : Bool
  /-- the agent reap took this task from, until another agent claims it (the Lua's `reaped_from`) -/
  reaped : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

structure Agent where
  st : ASt
  waiter : Bool
  big : Bool
  /-- idle 2+ min: lifecycle may end or reuse it -/
  aged : Bool
  /-- idle past the prompt cache with a big context -/
  cold : Bool
  boot : Bool
  /-- pool ids a digest told it of -/
  told : List Nat
  /-- ghost: tasks it thinks it holds -/
  believes : List Nat
  /-- the waiter's unread list between its read and its write (racy) -/
  snap : List Nat
  /-- the task whose deps `task claim` has read but not yet written (racy) -/
  reading : Nat
  /-- a background job of its own is running (a build, a model check, a Monitor) -/
  bg : Bool := false
  /-- agent.wt: the worktree it last edited in (the Edit hook sets it) -/
  wt : Option Nat := none
  /-- the worktrees it added, with their generation: their directory is named after it (`owned_wts`) -/
  own : List (Nat × Nat) := []
  /-- idle 30+ min (UNCLEAN_IDLE) -/
  stale : Bool
  /-- already nudged in this idle stretch -/
  nudged : Bool
  /-- the terminal is gone but the row isn't ended: it does nothing more, and the row still reads as live -/
  dead : Bool
  deriving DecidableEq, Repr, Inhabited

structure Lock where
  holder : Option Nat
  exp : Bool
  deriving DecidableEq, Repr, Inhabited

structure Msg where
  /-- none: the system or the communicator -/
  frm : Option Nat
  to : Nat
  urgent : Bool
  kind : Kind
  task : Nat
  deriving DecidableEq, Repr, Inhabited

/-- a linked worktree. Its process flag: some process's cwd is inside (machine.cwds) -/
structure Wt where
  on : Bool
  br : Option Nat
  head : Nat
  dirty : Bool
  proc : Bool
  /-- touched within SWEEP_IDLE (its directory or its HEAD log) -/
  recent : Bool
  /-- how many times the slot was added: a new one has a new path -/
  gen : Nat
  deriving DecidableEq, Repr, Inhabited

/-- a commit: its ancestors (itself included; history is a chain per commit) and its content, the patches it holds.
Every ordinary commit adds one fresh patch (a new file); a squash merge holds the union. -/
structure Commit where
  anc : List Nat
  cont : List Nat
  deriving DecidableEq, Repr, Inhabited

structure Git where
  wts : List Wt
  /-- branch tips; none: no such branch -/
  brs : List (Option Nat)
  cm : List Commit
  deriving DecidableEq, Repr, Inhabited

structure State where
  task : List Task
  ag : List Agent
  lock : List Lock
  log : List Msg
  cursor : List Nat
  /-- the log's length when the slot's agent was spawned -/
  start : List Nat
  /-- ghost: ids shown to each agent, in order -/
  seen : List (List Nat)
  /-- ghost: tasks whose unblock answer the holder hasn't seen -/
  pend : List Nat
  /-- ghost: some claim happened while a task it is after wasn't done -/
  early : Bool
  git : Git := default
  deriving DecidableEq, Repr, Inhabited

def Cfg.tasks (c : Cfg) : List Nat := List.range' 1 c.ntasks
def Cfg.agents (c : Cfg) : List Nat := List.range c.nagents
def Cfg.pat (c : Cfg) (p : Nat) : String := c.patterns.getD p ""

/-- locks.covers(path, pat): the path is the pattern, its glob, or under it as a directory (Glob.lean, lifted from
the Lua) -/
def covers (c : Cfg) (x pat : String) : Bool := Glob.covers c.lockForms x.toList pat.toList
/-- what a lock is for: some file both patterns cover (`Glob.overlaps_iff`) -/
def overlap (p q : String) : Bool := Glob.overlaps true p.toList q.toList
/-- what `swarm lock` refuses -/
def refuses (c : Cfg) (p q : String) : Bool :=
  if c.lockOverlap then Glob.overlaps c.lockForms p.toList q.toList else covers c p q || covers c q p

-- ---------- queries ----------
def State.tk (s : State) (t : Nat) : Task := if t = 0 then default else s.task.getD (t - 1) default
def State.agt (s : State) (a : Nat) : Agent := s.ag.getD a default
def State.owned (s : State) (o : Option Nat) : Agent := match o with | some a => s.agt a | none => default
def State.cur (s : State) (a : Nat) : Nat := s.cursor.getD a 0
def State.msg (s : State) (i : Nat) : Msg := if i = 0 then default else s.log.getD (i - 1) default
def Agent.live (g : Agent) : Bool := g.st != .unborn && g.st != .ended
def depsDone (s : State) (t : Nat) : Bool := (s.tk t).deps.all fun d => (s.tk d).st == .done
def startable (s : State) (t : Nat) : Bool := (s.tk t).st == .opn && depsDone s t
def pool (c : Cfg) (s : State) : List Nat := c.tasks.filter (startable s)
def held (k : Task) (a : Nat) : Bool := k.owner == some a && (k.st == .claimed || k.st == .blocked)
def holds (s : State) (a : Nat) : Bool := s.task.any (held · a)
def lockHeld (s : State) (a : Nat) : Bool := s.lock.any (·.holder == some a)
def members (s : State) : Nat := (s.ag.filter (·.live)).length
def addressed (s : State) (a i : Nat) : Bool := (s.msg i).to == a && (s.msg i).frm != some a
def unread (s : State) (a : Nat) : List Nat :=
  (List.range' (s.cur a + 1) (s.log.length - s.cur a)).filter (addressed s a)
/-- the waiter wakes the agent on a message: an urgent one always, others unless the agent is cold -/
def wakes (s : State) (a : Nat) : Bool :=
  let u := unread s a
  !u.isEmpty && (!(s.agt a).cold || u.any fun i => (s.msg i).urgent)
def nextTask (s : State) : Nat := (s.task.filter (·.st != .absent)).length + 1
/-- the slot a spawn fills: the first not live. An ended agent's slot is a new agent (the Lua's next name). -/
def nextAgent (c : Cfg) (s : State) : Option Nat := c.agents.find? fun a => !(s.agt a).live
/-- the cycle `task after` refuses: does t reach target along deps? -/
def reaches (c : Cfg) (s : State) (t target : Nat) : Bool :=
  ((List.range c.ntasks).foldl (fun r _ => r ++ r.flatMap fun x => (s.tk x).deps) [t]).contains target

-- ---------- git ----------
def Cfg.wtIds (c : Cfg) : List Nat := List.range c.nwts
/-- worktree w's own branch -/
def Cfg.wbr (c : Cfg) (w : Nat) : Nat := c.nbases + w
def Git.wt (g : Git) (w : Nat) : Wt := g.wts.getD w default
def Git.tip (g : Git) (b : Nat) : Option Nat := g.brs.getD b none
def Git.cmt (g : Git) (k : Nat) : Commit := g.cm.getD k default
def Git.tipOf (g : Git) (b : Nat) : Nat := (g.tip b).getD 0
/-- watchd.landed_ref(k, main): an ancestor of main, or the same content under other commits. Every ordinary commit adds
a fresh file and nothing is deleted, so both are "every patch of k is in main" -/
def Git.onMain (g : Git) (k : Nat) : Bool := (g.cmt k).cont.all (g.cmt (g.tipOf 0)).cont.contains
/-- watchd.landed(wt, main): clean and on main; a removed worktree has nothing to lose -/
def Git.landed (g : Git) (w : Nat) : Bool := let x := g.wt w; !x.on || (!x.dirty && g.onMain x.head)
/-- the protected refs: every base (`main`, and a swarm's own such as `formal`); `origin/*` is outside the model -/
def Cfg.bases (c : Cfg) : List Nat := List.range c.nbases
/-- k is reachable from branch b: `git merge-base --is-ancestor k b`, or b holds k's content under other commits (a squash
or rebase merge). Every ordinary commit adds a fresh patch and none deletes one, so an ancestor is a case of the second -/
def Git.reachFrom (g : Git) (k b : Nat) : Bool := (g.tip b).any fun t => (g.cmt k).cont.all (g.cmt t).cont.contains
/-- reachable from a protected ref: what workspace GC checks itself (never `git branch -d`, which asks HEAD or upstream) -/
def Git.safe (c : Cfg) (g : Git) (k : Nat) : Bool := c.bases.any (g.reachFrom k)
def Cfg.tbase (c : Cfg) (t : Nat) : Nat := c.taskBase.getD t 0
/-- clean, and its HEAD reachable from one of the branches `refs` (a removed worktree has nothing to lose) -/
def Git.landedIn (g : Git) (refs : List Nat) (w : Nat) : Bool := let x := g.wt w; !x.on || (!x.dirty && refs.any (g.reachFrom x.head))
/-- `base_for` of an agent: the bases of the tasks it owns (any state; a done task keeps its owner), main if none -/
def abases (c : Cfg) (s : State) (a : Nat) : List Nat :=
  match (c.tasks.filter fun t => (s.tk t).owner == some a).map c.tbase with
  | [] => [0]
  | bs => bs
/-- what the sweep protects: main, and the base of every task on the board -/
def pbases (c : Cfg) (s : State) : List Nat := 0 :: (c.tasks.filter fun t => (s.tk t).st != .absent).map c.tbase
/-- the landed checks: on main (`watchd.landed`), or with `perTaskBase` on one of `refs` -/
def landedC (c : Cfg) (g : Git) (refs : List Nat) (w : Nat) : Bool :=
  if c.perTaskBase then g.landedIn refs w else g.landed w
/-- some worktree has branch b checked out: git refuses to move it from elsewhere, or check it out twice -/
def Git.out (g : Git) (b : Nat) : Bool := g.wts.any fun x => x.on && x.br == some b
/-- owned_wts: w is there and its directory is named after a -/
def owns (s : State) (a w : Nat) : Bool := (s.git.wt w).on && (s.agt a).own.contains (w, (s.git.wt w).gen)
/-- conflict.wt_map: agent.wt, else the worktree with a branch of a's checked out -/
def wtmap (c : Cfg) (s : State) (a : Nat) : Option Nat :=
  match (s.agt a).wt with
  | some w => some w
  | none => ((s.agt a).own.find? fun (w, _) => owns s a w && (s.git.wt w).br == some (c.wbr w)).map (·.1)
/-- watchd.lifecycle's `unlanded`: work not on main in the worktree wt_map picks, or (PR #123) in any it owns -/
def unlanded (c : Cfg) (s : State) (a : Nat) : Bool :=
  (wtmap c s a).any (!landedC c s.git (abases c s a) ·) || (c.allWts && (s.agt a).own.any fun (w, _) => owns s a w && !landedC c s.git (abases c s a) w)

-- ---------- state changes (pure, so watchd's tick composes them) ----------
def setTask (s : State) (t : Nat) (f : Task → Task) : State :=
  if t = 0 then s else { s with task := s.task.modify (t - 1) f }
def setAg (s : State) (a : Nat) (f : Agent → Agent) : State := { s with ag := s.ag.modify a f }
def post (s : State) (m : Msg) : State := { s with log := s.log ++ [m] }

/-- one message shown to a: its effect on what a knows -/
def showMsg (s : State) (a id : Nat) : State :=
  let m := s.msg id
  let s1 := { s with seen := s.seen.modify a (· ++ [id]), cursor := s.cursor.modify a (max · id) }
  if m.kind == .answer && (s1.tk m.task).owner == some a then { s1 with pend := s1.pend.filter (· != m.task) }
  else if m.kind == .released then setAg s1 a fun g => { g with believes := g.believes.filter (· != m.task) }
  else s1
def showAll (s : State) (a : Nat) (ids : List Nat) : State := ids.foldl (showMsg · a ·) s
def deliver (s : State) (a : Nat) : State := showAll s a (unread s a)
/-- a takes t: it reads the task (task show), so an answer on it reaches a -/
def takes (c : Cfg) (s : State) (a t : Nat) : State :=
  let s1 := setAg s a fun g => { g with believes := t :: g.believes }
  if c.answerOnTask && (s1.tk t).answer then { s1 with pend := s1.pend.filter (· != t) } else s1
def claimed (s : State) (a t : Nat) : State :=
  setTask s t fun k => { k with st := .claimed, owner := some a, lease := true, reaped := if k.reaped == some a then k.reaped else none }
/-- the 350k fence on `task claim`: a big agent may take only what reap took from it -/
def fenced (c : Cfg) (s : State) (a t : Nat) : Bool := (s.agt a).big && !(c.retake && (s.tk t).reaped == some a)
/-- agents._release: every claim and lock of a -/
def releaseAll (s : State) (a : Nat) : State :=
  { s with
    task := s.task.map fun k => if held k a then { k with st := .opn, owner := none, lease := false, hcq := false } else k
    lock := s.lock.map fun l => if l.holder == some a then ⟨none, false⟩ else l }

/-- watchd.reap: does the owner of a claim past its lease keep it? -/
def keeps (c : Cfg) (g : Agent) : Bool :=
  match c.release with
  | .ended => g.live
  | .notWorking => g.st == .working
  | .idle => g.live && (g.st != .idle || (c.bgKeeps && g.bg))
/-- reap of one task: reopened, and its owner told -/
def reapTask (c : Cfg) (x : State) (t : Nat) : State :=
  let k := x.tk t
  match k.owner with
  | some o =>
    if k.st == .claimed && !k.lease && !keeps c (x.agt o) then
      post (setTask x t fun r => { r with st := .opn, owner := none, lease := false, reaped := some o }) ⟨none, o, false, .released, t⟩
    else x
  | none => x
def reapTasks (c : Cfg) (s : State) : State := c.tasks.foldl (reapTask c) s
def reapLocks (s : State) : State := { s with lock := s.lock.map fun l => if l.exp then ⟨none, false⟩ else l }
/-- idle and free of claims and locks: what lifecycle looks at before the worktrees -/
def idleFree (s : State) (a : Nat) : Bool :=
  let g := s.agt a
  g.st == .idle && g.aged && !holds s a && !lockHeld s a && g.reading == 0 && g.snap.isEmpty
def finished (c : Cfg) (s : State) (a : Nat) : Bool := idleFree s a && !unlanded c s a
/-- lifecycle's reusable agents: since PR #116 one told of the whole pool, its inbox read, has passed it over:
ended, not reusable; since PR #119 one with no live waiter (it would never read a digest) is ended too -/
def reusable (c : Cfg) (s : State) (a : Nat) : Bool :=
  let pl := pool c s
  finished c s a && !(s.agt a).big && !pl.isEmpty
    && !(c.passedOver && pl.all (s.agt a).told.contains && (unread s a).isEmpty)
    && ((s.agt a).waiter || !c.waiterAlive)
def endAgent (s : State) (a : Nat) : State :=
  releaseAll (setAg s a fun g => { g with st := .ended, boot := false, believes := [] }) a
/-- a spawn for task t into the first slot not live, while the roster has room -/
def spawnFor (c : Cfg) (pl : List Nat) (x : State) (t : Nat) : State :=
  match nextAgent c x with
  | some a =>
    if pl.contains t && members x < c.roster then
      let x1 := setAg x a fun _ => { (default : Agent) with st := .idle, boot := true }
      claimed { x1 with
        cursor := x1.cursor.set a x1.log.length
        start := x1.start.set a x1.log.length
        seen := x1.seen.set a [] } a t
    else x
  | none => x
/-- watchd.lifecycle: end finished agents, tell reusable ones about new work, else spawn into free slots -/
def lifecycle (c : Cfg) (s : State) : State :=
  let pl := pool c s
  let ended := c.agents.foldl (fun x a => if finished c s a && !reusable c s a then endAgent x a else x) s
  let told := c.agents.foldl (fun x a =>
    if reusable c s a && !pl.all (x.agt a).told.contains then
      post (setAg x a fun g => { g with told := pl ++ g.told }) ⟨none, a, false, .digest, 0⟩
    else x) ended
  if c.agents.any (reusable c s) then told else c.tasks.foldl (spawnFor c pl) told
/-- lifecycle ends a -/
def ends (c : Cfg) (s : State) (a : Nat) : Bool := finished c s a && !reusable c s a
/-- sweep's `used`: a live agent's agent.wt, or what wt_map picks for it -/
def used (c : Cfg) (s : State) (w : Nat) : Bool :=
  c.agents.any fun b => (s.agt b).live && ((s.agt b).wt == some w || wtmap c s b == some w)
/-- watchd.sweep_worktrees: unused, no process inside, untouched 30 min, clean and on main (`splitGC`: reachable from a
protected ref) -/
def sweeps (c : Cfg) (s : State) (w : Nat) : Bool :=
  let x := s.git.wt w
  x.on && !used c s w && !x.proc && !x.recent && (if c.splitGC then !x.dirty && s.git.safe c x.head else landedC c s.git (pbases c s) w)
/-- watchd.end_agent: the ended agent's wt_map worktree, unless a live peer's agent.wt is it; `git worktree remove`
refuses a dirty one. It looks at no process. -/
def endRemoves (c : Cfg) (s : State) (w : Nat) : Bool :=
  let x := s.git.wt w
  !c.splitGC && x.on && !x.dirty && c.agents.any (fun a => ends c s a && wtmap c s a == some w)
    && c.agents.all fun b => !((s.agt b).live && (s.agt b).wt == some w) || ends c s b
/-- `git worktree remove`, then `git branch -D` of the branch it had checked out unless that is main (`splitGC`: unless
it is a base or not reachable from one) -/
def Git.rm (c : Cfg) (g : Git) (w : Nat) : Git :=
  let x := g.wt w
  { g with wts := g.wts.set w { x with on := false },
           brs := match x.br with
             | some b => if b == 0 || (c.splitGC && (b < c.nbases || !g.safe c (g.tipOf b))) then g.brs else g.brs.set b none
             | none => g.brs }
/-- what the tick does to git: sweep (before lifecycle's decisions, which it doesn't change) and end_agent's removals -/
def gitTick (c : Cfg) (s : State) : Git :=
  c.wtIds.foldl (fun g w => if sweeps c s w || endRemoves c s w then g.rm c w else g) s.git
def tickOf (c : Cfg) (s : State) : State :=
  let r := reapLocks (reapTasks c s)
  { lifecycle c r with git := gitTick c r }

-- ---------- actions: `none` is "not enabled" ----------
def init (c : Cfg) : State where
  task := List.replicate c.ntasks default
  ag := c.agents.map fun a => { (default : Agent) with st := if a < c.roster then .working else .unborn }
  lock := c.patterns.map fun _ => default
  log := []
  cursor := c.agents.map fun _ => 0
  start := c.agents.map fun _ => 0
  seen := c.agents.map fun _ => []
  pend := []
  early := false
  git := { wts := List.replicate c.nwts default, brs := List.replicate c.nbases (some 0) ++ List.replicate c.nwts none,
           cm := [⟨[0], []⟩] }

def busy (s : State) (a : Nat) : Bool := (s.agt a).st == .working
/-- an agent runs a command only with an empty inbox: the PreToolUse hook delivers before every one -/
def working (s : State) (a : Nat) : Bool := busy s a && (unread s a).isEmpty
def ownsClaimed (s : State) (a t : Nat) : Bool := (s.tk t).st == .claimed && (s.tk t).owner == some a
def firstClaimed (c : Cfg) (s : State) (a : Nat) : Nat := (c.tasks.find? (ownsClaimed s a)).getD 0
def when (b : Bool) (s : State) : Option State := if b then some s else none
def unbelieve (s : State) (a t : Nat) : State := setAg s a fun g => { g with believes := g.believes.filter (· != t) }
def awake (s : State) (a : Nat) : State :=
  setAg s a fun g => { g with st := .working, waiter := false, aged := false, cold := false, stale := false, nudged := false }

/-- swarm task claim: refuses while a dependency isn't done, then writes `where state='open'` -/
def claim (c : Cfg) (s : State) (a t : Nat) : Option State :=
  when (!c.racy && working s a && startable s t && !fenced c s a t) (takes c (claimed s a t) a t)
/-- the same, as two steps: the dependency read, then the write -/
def claimRead (c : Cfg) (s : State) (a t : Nat) : Option State :=
  when (c.racy && working s a && (s.agt a).reading == 0 && startable s t && !fenced c s a t) (setAg s a ({ · with reading := t }))
def claimWrite (c : Cfg) (s : State) (a : Nat) : Option State :=
  let t := (s.agt a).reading
  when (c.racy && t > 0) <|
    if (s.tk t).st == .opn && (depsDone s t || !c.claimChecksDeps) then
      setAg { takes c (claimed s a t) a t with early := s.early || !depsDone s t } a ({ · with reading := 0 })
    else setAg s a ({ · with reading := 0 })
/-- the agent starts a background job, or it ends -/
def bgStart (s : State) (a : Nat) : Option State := when (busy s a && !(s.agt a).bg) (setAg s a ({ · with bg := true }))
def bgEnd (s : State) (a : Nat) : Option State := when ((s.agt a).live && (s.agt a).bg) (setAg s a ({ · with bg := false }))
def renew (s : State) (a t : Nat) : Option State :=
  when (working s a && ownsClaimed s a t) (setTask s t ({ · with lease := true }))
def release (s : State) (a t : Nat) : Option State :=
  when (working s a && ownsClaimed s a t)
    (unbelieve (setTask s t ({ · with st := .opn, owner := none, lease := false })) a t)
def block (s : State) (a t : Nat) : Option State :=
  when (working s a && ownsClaimed s a t) (setTask s t ({ · with st := .blocked }))
/-- swarm task done --evidence E: the CLI requires the flag; ev is whether E is non-empty -/
def done (c : Cfg) (s : State) (a t : Nat) (ev : Bool) : Option State :=
  when (working s a && ownsClaimed s a t && (ev || !c.evidenceRequired))
    (unbelieve (setTask s t ({ · with st := .done, lease := false, ev := ev })) a t)
/-- the owner drops its own claimed or blocked task -/
def dropOwn (s : State) (a t : Nat) : Option State :=
  when (working s a && held (s.tk t) a)
    (unbelieve (setTask s t ({ · with st := .dropped, owner := none, lease := false })) a t)
/-- swarm lock: refused while a live peer's lock (unexpired, holder not ended) is one `refuses` names -/
def lock (c : Cfg) (s : State) (a p : Nat) : Option State :=
  when (working s a && p < s.lock.length && (List.range s.lock.length).all fun q =>
      let l := s.lock.getD q default
      l.holder == none || l.holder == some a || l.exp || !(s.owned l.holder).live || !refuses c (c.pat p) (c.pat q))
    { s with lock := s.lock.set p ⟨some a, false⟩ }
def unlock (s : State) (a p : Nat) : Option State :=
  when (working s a && (s.lock.getD p default).holder == some a) { s with lock := s.lock.set p ⟨none, false⟩ }
def postTo (s : State) (a b : Nat) (urgent : Bool) : Option State :=
  when (working s a && b != a && (s.agt b).st != .unborn) (post s ⟨some a, b, urgent, .dm, 0⟩)
/-- swarm read, or a hook (prompt, post-tool): all unread, marked read -/
def readAll (s : State) (a : Nat) : Option State :=
  when (busy s a && !(unread s a).isEmpty) (deliver s a)
/-- the Stop hook: idle, a waiter armed, its context size known. A small-context agent with work in the pool
and no claim takes it first (brief: take the next task), so only a big or busy one stops beside the pool. -/
def stop (c : Cfg) (s : State) (a : Nat) (big : Bool) : Option State :=
  when (busy s a && (s.agt a).reading == 0 && (big || holds s a || (pool c s).isEmpty))
    (setAg s a ({ · with st := .idle, waiter := true, big := big, aged := false, cold := false, stale := false, nudged := false }))

-- the environment: time, the waiter, the human, hc
def wake (c : Cfg) (s : State) (a : Nat) : Option State :=
  when (!c.racy && (s.agt a).st == .idle && (s.agt a).waiter && wakes s a) (awake (deliver s a) a)
def wakeRead (c : Cfg) (s : State) (a : Nat) : Option State :=
  when (c.racy && (s.agt a).st == .idle && (s.agt a).waiter && (s.agt a).snap.isEmpty && wakes s a)
    (setAg s a ({ · with snap := unread s a }))
/-- the waiter's write, then the turn it starts: the prompt hook delivers whatever is still unread.
Since PR #115 the write fails if another delivery moved the cursor past what was read, and reads again. -/
def wakeWrite (c : Cfg) (s : State) (a : Nat) : Option State :=
  let snap := (s.agt a).snap
  when (c.racy && !snap.isEmpty) <|
    let x := if c.deliverCas && s.cur a ≥ snap.headD 0 then s else showAll s a snap
    setAg (awake (deliver x a) a) a ({ · with snap := [] })
/-- a turn the waiter didn't start (the human, a SendMessage nudge): the prompt hook delivers -/
def prompt (s : State) (a : Nat) : Option State :=
  when ((s.agt a).st == .idle && !(s.agt a).boot)
    (setAg (deliver s a) a ({ · with st := .working, aged := false, cold := false, stale := false, nudged := false }))
/-- a spawned agent's first turn: its brief says task show -/
def boot (c : Cfg) (s : State) (a : Nat) : Option State :=
  when ((s.agt a).boot && (s.agt a).st == .idle) <|
    let t := firstClaimed c s a
    let x := setAg (deliver s a) a ({ · with st := .working, boot := false })
    if t > 0 then takes c x a t else x
def waiterGone (s : State) (a : Nat) : Option State :=
  when (s.agt a).waiter (setAg s a ({ · with waiter := false }))
def age (s : State) (a : Nat) : Option State :=
  when ((s.agt a).st == .idle && !(s.agt a).aged) (setAg s a ({ · with aged := true }))
def cool (s : State) (a : Nat) : Option State :=
  let g := s.agt a
  when (g.st == .idle && g.aged && g.big && !g.cold) (setAg s a ({ · with cold := true }))
/-- an agent's git commands, in a worktree it owns (`add`: one it makes) -/
inductive GitOp where
  /-- `git worktree add -b <name>/.. <dir named after it> main`. A second one only once it has edited (so wt_map's
  fallback has one candidate) -/
  | add (w : Nat)
  /-- writes a new file; the Edit hook sets agent.wt -/
  | edit (w : Nat)
  | commit (w : Nat)
  /-- `git push . HEAD:<b>`: fast-forward base b -/
  | land (w b : Nat)
  /-- a squash merge of HEAD into base b -/
  | squash (w b : Nat)
  /-- `git checkout <b>`: a base, or the worktree's own branch -/
  | checkout (w b : Nat)
  deriving DecidableEq, Repr

def Git.setWt (g : Git) (w : Nat) (f : Wt → Wt) : Git := { g with wts := g.wts.modify w f }
def Git.setBr (g : Git) (b k : Nat) : Git := { g with brs := g.brs.set b (some k) }
def Git.next (g : Git) : Nat := g.cm.length
/-- a new commit on top of k: a fresh patch -/
def Git.mkCommit (g : Git) (k : Nat) : Git := { g with cm := g.cm ++ [⟨g.next :: (g.cmt k).anc, g.next :: (g.cmt k).cont⟩] }
/-- a squash merge of h onto k -/
def Git.mkSquash (g : Git) (k h : Nat) : Git :=
  let ck := (g.cmt k).cont
  { g with cm := g.cm ++ [⟨g.next :: (g.cmt k).anc, ck ++ (g.cmt h).cont.filter (!ck.contains ·)⟩] }

/-- whether the command can run, the new git state, and the agent's agent.wt and worktrees after it -/
def gitDo (c : Cfg) (s : State) (a : Nat) : GitOp → Bool × Git × Option Nat × List (Nat × Nat)
  | .add w =>
    let g := s.git
    let x := g.wt w
    let m := g.tipOf 0
    (w < c.nwts && !x.on && ((s.agt a).wt.isSome || !(s.agt a).own.any fun (v, _) => owns s a v),
      (g.setWt w fun _ => ⟨true, some (c.wbr w), m, false, false, true, x.gen + 1⟩).setBr (c.wbr w) m,
      (s.agt a).wt, (w, x.gen + 1) :: (s.agt a).own)
  | .edit w => (owns s a w, s.git.setWt w ({ · with dirty := true, recent := true }), some w, (s.agt a).own)
  | .commit w =>
    let g := s.git
    let x := g.wt w
    let g1 := (g.mkCommit x.head).setWt w ({ · with head := g.next, dirty := false, recent := true })
    (owns s a w && x.dirty, match x.br with | some b => g1.setBr b g.next | none => g1, (s.agt a).wt, (s.agt a).own)
  | .land w b =>
    let g := s.git
    let h := (g.wt w).head
    (owns s a w && b < c.nbases && (g.tip b).isSome && (g.cmt h).anc.contains (g.tipOf b) && h != g.tipOf b && !g.out b,
      g.setBr b h, (s.agt a).wt, (s.agt a).own)
  | .squash w b =>
    let g := s.git
    let h := (g.wt w).head
    let k := g.tipOf b
    (owns s a w && b < c.nbases && (g.tip b).isSome && !(g.cmt h).cont.all (g.cmt k).cont.contains && !g.out b,
      (g.mkSquash k h).setBr b g.next, (s.agt a).wt, (s.agt a).own)
  | .checkout w b =>
    let g := s.git
    (owns s a w && (b < c.nbases && !c.recordedWorkspaces || b == c.wbr w) && (g.tip b).isSome && !g.out b,
      g.setWt w ({ · with br := some b, head := g.tipOf b, recent := true }), (s.agt a).wt, (s.agt a).own)
def gitCmd (c : Cfg) (s : State) (a : Nat) (op : GitOp) : Option State :=
  let r := gitDo c s a op
  when (working s a && r.1) (setAg { s with git := r.2.1 } a fun g => { g with wt := r.2.2.1, own := r.2.2.2 })

/-- the world in a worktree: 30 min pass untouched, or a process's cwd moves in or out -/
inductive WOp where | age | proc (v : Bool)
  deriving DecidableEq, Repr
def WOp.ok (x : Wt) : WOp → Bool | .age => x.recent | .proc v => x.proc != v
def WOp.f : WOp → Wt → Wt | .age, x => { x with recent := false } | .proc v, x => { x with proc := v }
def world (s : State) (w : Nat) (op : WOp) : Option State :=
  when ((s.git.wt w).on && op.ok (s.git.wt w)) { s with git := s.git.setWt w op.f }
def stale (s : State) (a : Nat) : Option State :=
  when ((s.agt a).st == .idle && (s.agt a).aged && !(s.agt a).stale) (setAg s a ({ · with stale := true }))
/-- watchd.unclean: idle 30 min, kept only by an unclean worktree, with a live waiter: one urgent message per stretch -/
def nudge (c : Cfg) (s : State) (a : Nat) : Option State :=
  let g := s.agt a
  when (c.uncleanNudge && idleFree s a && unlanded c s a && g.stale && g.waiter && !g.nudged)
    (post (setAg s a ({ · with nudged := true })) ⟨none, a, true, .nudge, 0⟩)
/-- the owner of `t` has not had its first turn -/
def bootingOwner (s : State) (t : Nat) : Bool := match (s.tk t).owner with | some o => (s.agt o).boot | none => false
def expire (c : Cfg) (s : State) (t : Nat) : Option State :=
  when ((s.tk t).st == .claimed && (s.tk t).lease && !(c.bootFirst && bootingOwner s t)) (setTask s t ({ · with lease := false }))
def expireLock (s : State) (p : Nat) : Option State :=
  let l := s.lock.getD p default
  when (l.holder != none && !l.exp) { s with lock := s.lock.set p { l with exp := true } }
/-- swarm leave, or reap of a dead terminal: ended, its claims and locks released -/
def leaveIf (ok : Bool) (s : State) (a : Nat) : Option State :=
  let g := s.agt a
  when (ok && g.live && g.reading == 0 && g.snap.isEmpty) (endAgent (setAg s a ({ · with waiter := false })) a)
def leave (s : State) (a : Nat) : Option State := leaveIf true s a

/-- the terminal dies with no `swarm leave` and no reap: the row stays as it was -/
def die (s : State) (a : Nat) : Option State :=
  let g := s.agt a
  when (g.live && !g.dead && g.reading == 0 && g.snap.isEmpty) (setAg s a ({ · with dead := true, waiter := false, bg := false }))
/-- watchd's reap ends a row whose bound terminal `hc ls` no longer lists (the `live_addrs` branch of `reap`) -/
def reapGone (c : Cfg) (s : State) (a : Nat) : Option State :=
  leaveIf (c.watchd && c.hcSees && !c.unbound.contains a && (s.agt a).dead) s a
/-- watchd sees an hc permission prompt: the agent and its first claimed task go blocked -/
def hcPrompt (c : Cfg) (s : State) (a : Nat) : Option State :=
  when (busy s a && (s.agt a).reading == 0)
    (setTask (setAg s a ({ · with st := .blocked })) (firstClaimed c s a) ({ · with st := .blocked, hcq := true }))
/-- the prompt is answered: its tasks are claimed again with a fresh lease; the next tool's hook delivers -/
def hcClear (s : State) (a : Nat) : Option State :=
  when ((s.agt a).st == .blocked) <|
    let x := { s with task := s.task.map fun k =>
      if k.owner == some a && k.st == .blocked && k.hcq then { k with st := .claimed, hcq := false, lease := true } else k }
    setAg (deliver x a) a ({ · with st := .working })

-- the communicator
def add (s : State) (deps : List Nat) : Option State :=
  let t := nextTask s
  when (t ≤ s.task.length && deps.all (· < t)) (setTask s t ({ · with st := .opn, deps := deps }))
def after (c : Cfg) (s : State) (t : Nat) (deps : List Nat) : Option State :=
  when ((s.tk t).st == .opn && deps.all fun d => (s.tk d).st != .absent && !reaches c s d t)
    (setTask s t ({ · with deps := deps }))
def unblock (c : Cfg) (s : State) (t : Nat) : Option State :=
  match (s.tk t).owner with
  | some o => when ((s.tk t).st == .blocked) <|
    let x := setTask s t fun k => { k with st := .claimed, lease := true, hcq := false, answer := k.answer || c.answerOnTask }
    { post x ⟨none, o, false, .answer, t⟩ with pend := t :: x.pend }
  | none => none
/-- swarm task drop by the communicator: any task, in any state (a done one too) -/
def drop (s : State) (t : Nat) : Option State :=
  when ((s.tk t).st != .absent && (s.tk t).st != .dropped)
    (setTask s t ({ · with st := .dropped, owner := none, lease := false, hcq := false }))
/-- watchd --once -/
def tick (c : Cfg) (s : State) : Option State := when (c.watchd && tickOf c s != s) (tickOf c s)

/-- Everything that can happen: the agents' commands, the environment, the communicator, watchd. -/
inductive Action where
  | bgStart (a : Nat) | bgEnd (a : Nat)
  | claim (a t : Nat) | claimRead (a t : Nat) | claimWrite (a : Nat) | renew (a t : Nat) | release (a t : Nat)
  | block (a t : Nat) | done (a t : Nat) (ev : Bool) | dropOwn (a t : Nat) | lock (a p : Nat) | unlock (a p : Nat)
  | postTo (a b : Nat) (urgent : Bool) | readAll (a : Nat) | stop (a : Nat) (big : Bool)
  | wake (a : Nat) | wakeRead (a : Nat) | wakeWrite (a : Nat) | prompt (a : Nat) | boot (a : Nat)
  | git (a : Nat) (op : GitOp) | world (w : Nat) (op : WOp) | stale (a : Nat) | nudge (a : Nat)
  | waiterGone (a : Nat) | age (a : Nat) | cool (a : Nat) | expire (t : Nat) | expireLock (p : Nat) | leave (a : Nat)
  | hcPrompt (a : Nat) | hcClear (a : Nat) | die (a : Nat) | reapGone (a : Nat)
  | add (deps : List Nat) | after (t : Nat) (deps : List Nat) | unblock (t : Nat) | drop (t : Nat) | tick
  deriving DecidableEq, Repr

def step (c : Cfg) (s : State) : Action → Option State
  | .bgStart a => bgStart s a | .bgEnd a => bgEnd s a
  | .claim a t => claim c s a t | .claimRead a t => claimRead c s a t | .claimWrite a => claimWrite c s a
  | .renew a t => renew s a t | .release a t => release s a t | .block a t => block s a t
  | .done a t ev => done c s a t ev | .dropOwn a t => dropOwn s a t | .lock a p => lock c s a p
  | .unlock a p => unlock s a p | .postTo a b u => postTo s a b u | .readAll a => readAll s a
  | .stop a big => stop c s a big | .wake a => wake c s a | .wakeRead a => wakeRead c s a
  | .wakeWrite a => wakeWrite c s a | .prompt a => prompt s a | .boot a => boot c s a
  | .git a op => gitCmd c s a op | .world w op => world s w op | .stale a => stale s a | .nudge a => nudge c s a
  | .waiterGone a => waiterGone s a | .age a => age s a | .cool a => cool s a | .expire t => expire c s t
  | .expireLock p => expireLock s p | .leave a => leave s a | .hcPrompt a => hcPrompt c s a
  | .hcClear a => hcClear s a | .die a => die s a | .reapGone a => reapGone c s a | .add deps => add s deps | .after t deps => after c s t deps
  | .unblock t => unblock c s t | .drop t => drop s t | .tick => tick c s

/-- The states the system can be in. -/
inductive Reachable (c : Cfg) : State → Prop
  | init : Reachable c (init c)
  | step {s s' : State} (act : Action) : Reachable c s → step c s act = some s' → Reachable c s'

/-- A run from the start: the state after the actions, if each was enabled. -/
def run (c : Cfg) (acts : List Action) : Option State := acts.foldlM (step c) (init c)

theorem reachable_of_run {c : Cfg} {acts : List Action} {s : State} (h : run c acts = some s) : Reachable c s := by
  suffices ∀ (acts : List Action) (s0 s : State), Reachable c s0 → acts.foldlM (step c) s0 = some s → Reachable c s from
    this acts _ s .init h
  intro acts
  induction acts with
  | nil => intro s0 s h0 h; simp [List.foldlM] at h; exact h ▸ h0
  | cons a as ih =>
    intro s0 s h0 h
    simp only [List.foldlM_cons, Option.bind_eq_bind] at h
    cases h1 : step c s0 a with
    | none => simp [h1] at h
    | some s1 => rw [h1] at h; exact ih s1 s (.step a h0 h1) h

-- ---------- safety, as checks of one state ----------
def active (g : Agent) : Bool := g.st == .working || g.st == .blocked
/-- S1. No task has two agents at work on it: no two agents, each working or at an hc prompt, both believe they hold it. -/
def oneWorker (s : State) : Bool :=
  let n := List.range s.ag.length
  n.all fun a => n.all fun b => a == b ||
    !(active (s.agt a) && active (s.agt b) && (s.agt a).believes.any (s.agt b).believes.contains)
/-- S2. No task starts before the tasks it is after are done. -/
def noEarlyStart (s : State) : Bool := !s.early
/-- S3. No two live locks of different agents cover a common file. -/
def locksDisjoint (c : Cfg) (s : State) : Bool :=
  let n := List.range s.lock.length
  n.all fun p => n.all fun q =>
    let l := s.lock.getD p default
    let m := s.lock.getD q default
    !(p != q && l.holder != none && m.holder != none && l.holder != m.holder && !l.exp && !m.exp
      && (s.owned l.holder).live && (s.owned m.holder).live && overlap (c.pat p) (c.pat q))
/-- S4. A message is never shown twice, and a cursor never passes one it didn't show. -/
def inboxExact (s : State) : Bool := (List.range s.ag.length).all fun a =>
  let seen := s.seen.getD a []
  decide (seen.Pairwise (· < ·)) &&
    (List.range' (s.start.getD a 0 + 1) (s.cur a - s.start.getD a 0)).all fun i => !addressed s a i || seen.contains i
/-- S5. A done task has evidence. -/
def doneHasEvidence (s : State) : Bool := s.task.all fun k => k.st != .done || k.ev

-- ---------- workspaces (sw-bases) ----------
/-- W1, of a step from s to git g': each worktree it removes was clean, unattached (no live agent's agent.wt or wt_map
pick), had no process inside and its HEAD reachable from a protected ref; each branch it deletes is no protected ref
and its tip was reachable from one -/
def gcOk (c : Cfg) (s : State) (g' : Git) : Bool :=
  let g := s.git
  c.wtIds.all (fun w => let x := g.wt w
    !(x.on && !(g'.wt w).on) || (!x.dirty && !used c s w && !x.proc && g.safe c x.head))
  && (List.range g.brs.length).all fun b =>
    !((g.tip b).isSome && (g'.tip b).isNone) || (decide (c.nbases ≤ b) && g.safe c (g.tipOf b))
/-- what workspace GC alone does to git in a tick: the sweep -/
def sweepGit (c : Cfg) (s : State) : Git := c.wtIds.foldl (fun g w => if sweeps c s w then g.rm c w else g) s.git
/-- W2: a tick does to git only what the sweep does: ending an agent removes no worktree and deletes no branch -/
def endKeepsGit (c : Cfg) (s : State) : Bool := let r := reapLocks (reapTasks c s); gitTick c r == sweepGit c r
/-- W3, the workspace half: w is there, clean, its HEAD on a protected ref, unattached, no process inside, untouched -/
def orphan (c : Cfg) (s : State) (w : Nat) : Bool :=
  let x := s.git.wt w
  w < c.nwts && x.on && !x.dirty && s.git.safe c x.head && !used c s w && !x.proc && !x.recent
/-- W3, the agent half: idle, free of claims and locks, and every worktree it owns clean with its HEAD on a base -/
def doneOnBase (c : Cfg) (s : State) (a : Nat) : Bool :=
  idleFree s a && (s.agt a).own.all fun (w, _) => !owns s a w || (!(s.git.wt w).dirty && s.git.safe c (s.git.wt w).head)
/-- W4: no worktree has a base checked out (so no base is ever refused to `git push . HEAD:<base>`) -/
def noBaseOut (c : Cfg) (s : State) : Bool :=
  c.wtIds.all fun w => let x := s.git.wt w; !(x.on && x.br.any (· < c.nbases))

-- ---------- what liveness speaks of ----------
def slotFree (c : Cfg) (s : State) : Bool := members s < c.roster
def idleClaim (s : State) (a t : Nat) : Bool := ownsClaimed s a t && (s.agt a).st == .idle
def answered (s : State) (t : Nat) : Bool := !s.pend.contains t || (s.tk t).st == .done || (s.tk t).st == .dropped

/-- what cli_model_spec.lua drives the CLI with (atomic commands; Traces.lean leaves hc and leave out) -/
def replay : Cfg := { nagents := 4, ntasks := 4, patterns := ["m/*.lua", "m/a*", "m/", "m/a.lua"], nwts := 3, nbases := 2, perTaskBase := true, splitGC := true, taskBase := [0, 0, 1, 0, 1] }

end Swarm
