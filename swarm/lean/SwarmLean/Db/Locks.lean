import SwarmLean.Db.Tasks
import SwarmLean.Db.Sels
import SwarmModel.Glob

/-! locks.lua's pure parts: covers and overlaps (swarm/model's Glob.lean, proved there), the lock holder, an agent's
task line, and lock/unlock as steps; and as statement-store transactions (sw-global §3): keyed reads of one repo's
locks and their holders, the step as the decision, its plan. A lock is keyed by (repo, path) and holds for every swarm
in its repo. -/

namespace SwarmLean.Locks
open Agents

/-- A path in a repo: the repo (its main worktree's toplevel, `lock.repo`) and the path relative to the toplevel of
the worktree it is in. -/
structure InRepo where
  repo : String
  rel : String
  deriving DecidableEq, Repr, Inhabited

/-- The live, unexpired locks in `repo` of agents other than `me`, in load order (lock_holder's and cmd_lock's join). -/
def others (db : Db) (repo me : String) (now : Int) : List Lock :=
  db.locks.filter fun l => l.repo == repo && (match l.agent with
    | some a => a != me && l.lease_until.any (· > now) && db.agents.any fun g => g.name == a && g.ended.isNone
    | none => false)

/-- Another live agent's lock that covers `p` in its repo (locks.lock_holder). -/
def lockHolder (db : Db) (me : String) (p : InRepo) (now : Int) : Option Lock :=
  (others db p.repo me now).find? fun l => covers p.rel l.path

/-- `task #N: title` of the first task `name` holds, else `no claimed task` (locks.task_of). -/
def taskOf (db : Db) (name : String) : String :=
  let held := db.tasks.filter fun t => t.owner == some name && (t.status = .inProgress || t.status = .needsInput)
  match held.mergeSort (·.id ≤ ·.id) with
  | t :: _ => s!"task #{d t.id}: {t.title.getD ""}"
  | [] => "no claimed task"

/-- `swarm lock` on `p`: refused for an ended agent (a lock `swarm join` would bring back unchecked) or when it
overlaps a live peer's lock in the same repo; else this agent's lock (insert or replace). An error leaves the db as it
was (the Lua's transaction rolls back). -/
def lock (c : Tasks.Ctx) (p : InRepo) (reason lease : String) (db0 : Db) : Db × Except String Unit :=
  if let some (.ended ..) := fence db0 c.me c.here then (db0, .error s!"{c.me} was ended; `swarm join` to return.") else
  let db := touch db0 c.me none c.here c.now
  match (others db p.repo c.me c.now).find? fun o => overlaps p.rel o.path with
  | some o => (db0, .error s!"{p.rel} overlaps {o.path}, locked by {o.agent.getD ""}; message it")
  | none => match dur lease with
    | none => (db0, .error s!"bad duration '{lease}' (use 90s, 30m, 2h)")
    | some l =>
      let row : Lock := { repo := p.repo, path := p.rel, agent := some c.me, reason := some reason, since := some c.now,
                          lease_until := some (c.now + l), seen := some 0 }
      let db := { db with locks := db.locks.filter (fun (x : Lock) => !(x.repo == p.repo && x.path == p.rel)) ++ [row] }
      (db.log c.now (some c.me) "lock" (some p.rel) (some reason), .ok ())

/-- `swarm unlock`: drops this agent's lock on `p`, if it has one. -/
def unlock (me : String) (p : InRepo) (now : Int) (db : Db) : Db :=
  let db := { db with locks := db.locks.filter fun l => !(l.repo == p.repo && l.path == p.rel && l.agent == some me) }
  db.log now (some me) "unlock" (some p.rel) none

/-! ## The transactions -/

/-- The lock on `p`, whoever holds it. -/
def atSel (p : InRepo) : Sel :=
  { table := .lock, cond := .and (.eq "repo" (.text p.repo)) (.eq "path" (.text p.rel)) }

/-- The unexpired locks in `repo` of agents other than `me`. -/
def othersSel (repo me : String) (now : Int) : Sel :=
  { table := .lock, cond := .and (.eq "repo" (.text repo)) (.and (.gt "lease_until" (.int now)) (.ne "agent" (.text me))) }

/-- The rows of the agents holding locks `ls`, but `me`, in any swarm: a lock holds for every swarm in its repo
(sw-global §2). -/
def holders (ls : List Lock) (me : String) : Txn (List Agent) := do
  let hs := ((ls.filterMap (·.agent)).filter (· != me)).eraseDups
  if hs.isEmpty then return []
  return (← Txn.slice [{ table := .agent, cond := .oneOf "name" (hs.map .text), inScope := false }]).agents

/-- Another live agent's lock that covers `p` (`lockHolder`), read by key: the unexpired locks of others in its repo,
then their holders' rows. -/
def holderTxn (me : String) (p : InRepo) (now : Int) : Txn (Option Lock) := do
  let d ← Txn.slice [othersSel p.repo me now]
  let a ← holders d.locks me
  return lockHolder { d with agents := a } me p now

/-- `swarm lock` (`lock`): reads what `touch` reads of the agent, the lock on `p` and the unexpired locks of others in
its repo, then their holders' rows; writes the step's plan. -/
def lockTxn (c : Tasks.Ctx) (p : InRepo) (reason lease : String) : Txn (Except String Unit) := do
  let ss := Sels.touch c.me ++ [atSel p, othersSel p.repo c.me c.now]
  let d ← Txn.slice ss
  let d ← if (d.agent c.me).isSome then pure d else Txn.slice ss [.msg]
  let d := { d with agents := sortRows (d.agents ++ (← holders d.locks c.me)) }
  let (d', r) := lock c p reason lease d
  Txn.exec (slicePlan d d')
  return r

/-- `swarm unlock` (`unlock`): reads the lock on `p`, writes the step's plan. -/
def unlockTxn (me : String) (p : InRepo) (now : Int) : Txn Unit :=
  Txn.update [atSel p] [] fun d => (unlock me p now d, ())

end SwarmLean.Locks
