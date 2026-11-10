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
  /-- the worktree wt_map picks holds work not on main, and another worktree it owns does -/
  wt1 : Bool
  wt2 : Bool
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
  deriving DecidableEq, Repr, Inhabited

def Cfg.tasks (c : Cfg) : List Nat := List.range' 1 c.ntasks
def Cfg.agents (c : Cfg) : List Nat := List.range c.nagents
def Cfg.pat (c : Cfg) (p : Nat) : String := c.patterns.getD p ""

/-- locks.covers(path, pat) for the strings the instances use, from the Lua's rule: equal, fnmatch (no
FNM_PATHNAME), or under the pattern as a directory. The replay checks the CLI agrees. -/
def covers (x pat : String) : Bool := [
  ("m/", "m/"), ("m/a.lua", "m/"), ("m/*.lua", "m/"), ("m/a*", "m/"), ("m/b.lua", "m/"), ("m/a.txt", "m/"),
  ("m/a.lua", "m/a.lua"), ("m/b.lua", "m/b.lua"),
  ("m/a.lua", "m/*.lua"), ("m/*.lua", "m/*.lua"), ("m/b.lua", "m/*.lua"),
  ("m/a.lua", "m/a*"), ("m/a*", "m/a*"), ("m/a.txt", "m/a*")].contains (x, pat)
/-- what a lock is for: some file both patterns cover -/
def overlap (p q : String) : Bool := ["m/a.lua", "m/b.lua", "m/a.txt"].any fun f => covers f p && covers f q
/-- what `swarm lock` refuses -/
def refuses (c : Cfg) (p q : String) : Bool := if c.lockOverlap then overlap p q else covers p q || covers q p

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
/-- watchd.lifecycle's `unlanded`: work not on main in a worktree the agent owns (all of them since PR #123) -/
def unlanded (c : Cfg) (g : Agent) : Bool := g.wt1 || (c.allWts && g.wt2)
/-- idle and free of claims and locks: what lifecycle looks at before the worktrees -/
def idleFree (s : State) (a : Nat) : Bool :=
  let g := s.agt a
  g.st == .idle && g.aged && !holds s a && !lockHeld s a && g.reading == 0 && g.snap.isEmpty
def finished (c : Cfg) (s : State) (a : Nat) : Bool := idleFree s a && !unlanded c (s.agt a)
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
def tickOf (c : Cfg) (s : State) : State := lifecycle c (reapLocks (reapTasks c s))

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
/-- the agent's work leaves main behind in worktree 1 (the one wt_map picks) or 2, or lands -/
def dirty (s : State) (a : Nat) (second : Bool) (v : Bool) : Option State :=
  when (working s a) (setAg s a fun g => if second then { g with wt2 := v } else { g with wt1 := v })
def stale (s : State) (a : Nat) : Option State :=
  when ((s.agt a).st == .idle && (s.agt a).aged && !(s.agt a).stale) (setAg s a ({ · with stale := true }))
/-- watchd.unclean: idle 30 min, kept only by an unclean worktree, with a live waiter: one urgent message per stretch -/
def nudge (c : Cfg) (s : State) (a : Nat) : Option State :=
  let g := s.agt a
  when (c.uncleanNudge && idleFree s a && unlanded c g && g.stale && g.waiter && !g.nudged)
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
  | dirty (a : Nat) (second v : Bool) | stale (a : Nat) | nudge (a : Nat)
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
  | .dirty a w v => dirty s a w v | .stale a => stale s a | .nudge a => nudge c s a
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

-- ---------- what liveness speaks of ----------
def slotFree (c : Cfg) (s : State) : Bool := members s < c.roster
def idleClaim (s : State) (a t : Nat) : Bool := ownsClaimed s a t && (s.agt a).st == .idle
def answered (s : State) (t : Nat) : Bool := !s.pend.contains t || (s.tk t).st == .done || (s.tk t).st == .dropped

/-- what cli_model_spec.lua drives the CLI with (atomic commands; Traces.lean leaves hc and leave out) -/
def replay : Cfg := { nagents := 4, ntasks := 4, patterns := ["m/*.lua", "m/a*", "m/", "m/a.lua"] }

end Swarm
