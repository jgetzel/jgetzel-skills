import SwarmLean.Db.Queue
import SwarmLean.Db.Notes
import SwarmLean.Db.Sels

/-! The task and queue commands on the statement store (sw-global §3): each reads the rows its pure step (Tasks.lean,
Queue.lean, Notes.lean) looks at, by key or filter, runs the step on that slice and writes its difference. A claim
takes its task by a guarded update (its state and assignee as read), so of two claimers only one wins. -/

namespace SwarmLean.TaskTxn
open Sqlite (Val)
open Tasks Agents

/-- Task `id`. -/
def task (id : Int) : Sel := { table := .task, cond := .eq "id" (.int id) }

/-- The tasks of ids `ids`. -/
def tasks (ids : List Int) : Sel := { table := .task, cond := .oneOf "id" (ids.map .int) }

/-- The tasks not done: every task a dependency can wait on, and the pool's. -/
def undoneSel : Sel := { table := .task, cond := .ne "state" (.text Status.completed.text) }

/-- The tasks with a place: every task not closed. -/
def queuedSel : Sel := { table := .task, cond := .notNull "qpos" }

/-- The Ready and Backlog tasks with deps: every task `waiters` can name. -/
def waitingSel : Sel :=
  { table := .task, cond := .and (.oneOf "state" [.text Status.ready.text, .text Status.backlog.text]) (.notNull "deps") }

/-- Every task. -/
def allTasks : Sel := { table := .task }

/-- An event's data names task `id` (`eventTask`), or a task whose id starts with its digits. -/
def about (id : Int) : Cond := .or (.pre "data" ("#" ++ d id)) (.pre "data" ("auto #" ++ d id))

/-- The events of kinds `ks` about task `id` (a superset `eventTask` narrows). -/
def evs (id : Int) (ks : List String := TASK_KINDS) : Sel :=
  { table := .event, cond := .and (.oneOf "kind" (ks.map .text)) (about id) }

/-- The agents and cursors `stopPending` reads for tasks `ts`: those their stops went to, in any swarm (a task is the
machine's, and agent names are unique on it). -/
def stops (ts : List Task) : List Sel :=
  let ns := (ts.filterMap fun t => py t.stop_to).eraseDups.map Val.text
  if ns.isEmpty then [] else
    [{ table := .agent, cond := .oneOf "name" ns, inScope := false }, { table := .cursor, cond := .oneOf "agent" ns }]

/-- The ids reachable from `ids` along deps, `ids` among them: a frontier read at a time. -/
def closure (ids : List Int) : Txn (List Int) := go 100000 [] ids
where
  go : Nat → List Int → List Int → Txn (List Int)
    | 0, seen, _ => pure seen
    | fuel + 1, seen, front => do
      let front := (Queue.dedup front).filter (!seen.contains ·)
      if front.isEmpty then return seen
      let s ← Txn.slice [tasks front]
      go fuel (seen ++ front) (s.tasks.flatMap depsOf)

/-- What `pool` and `staffing` read: the tasks not done, the queue, and the agents and cursors of their stops. -/
def poolSels : Txn (List Sel) := do
  let s ← Txn.slice [undoneSel, queuedSel]
  return [undoneSel, queuedSel] ++ stops s.tasks

/-- Task `id`'s step `f` on task `id` and what `more` says to read of it as it is now (nothing when it is missing). -/
def onTask (id : Int) (next : List Table) (more : Task → Txn (List Sel)) (f : Db → Db × α) : Txn α := do
  let s ← Txn.slice [task id]
  let ss ← match s.find id with
    | some r => more r
    | none => pure []
  Txn.update (task id :: ss) next f

/-- The agent rows named `ns` (a role, a post's addressee), in any swarm: a task's owner or lander may be another
swarm's. -/
def agents (ns : List (Option String)) : List Sel :=
  match (ns.filterMap py).eraseDups with
  | [] => []
  | l => [{ table := .agent, cond := .oneOf "name" (l.map .text), inScope := false }]

/-- `task add`: its deps, the creator's held tasks, the places (a new task goes to the end of Ready) and the next
task id. -/
def add (c : Ctx) (a : AddArgs) : Txn (Except String Nat) :=
  Txn.update ([tasks a.deps, Sels.owned c.me, queuedSel] ++ (if a.parent.isSome then [allTasks] else [])) [.task] (Tasks.add c a)

/-- The claim of task `id` on its slice: the task's row by a guarded update, then the rest with the
held notes taken (`Notes.takeHeld`). -/
def claimTxn (c : Ctx) (id : Int) (lease : String) : Txn (Except String (Claimed × List Msg)) := do
  let box := Notes.box id
  let s ← Txn.slice [task id, Sels.cursor box]
  let some r := s.find id | return .error s!"no task #{d id}"
  let notes : Cond := .and (.gt "id" (.int (Msgs.cursorOf s box))) (.oneOf "dest" [.text box, .text "@all"])
  let reap : Cond := .and (Sels.evOf c.me "reap") (.eq "data" (.text s!"task #{d id} lease expired"))
  let ss := [task id, tasks (depsOf r), Sels.metas ["comms", "ctx_nudge"], evs id ["claim", "spawn"],
    { table := .event, cond := reap }, Sels.cursor box, { table := .msg, cond := notes }] ++ Sels.touch c.me ++ stops [r]
  let d0 ← Txn.slice ss [.msg]
  let (d1, res) := claim c id lease d0
  match res, d1.find id with
  | .ok cl, some t =>
    let won ← Txn.guarded (Row.put t) (.and (.eq "state" (.text r.status.text))
      (match r.assignee with | some a => .eq "owner" (.text a) | none => .null "owner"))
    if !won then return .error s!"task #{d id} was taken under you; `swarm task show {d id}`"
    let (d2, ns) := Notes.takeHeld c.me c.now id d1
    Txn.exec (slicePlan { d0 with tasks := d1.tasks } d2)
    return .ok (cl, ns)
  | .ok _, none => return .error s!"no task #{d id}"
  | .error e, _ =>
    Txn.exec (slicePlan d0 d1)
    return .error e

/-- `task after`: the task and every task its new deps reach. -/
def after (c : Ctx) (id : Int) (deps : List Int) : Txn (Except String Unit) := do
  Txn.update [allTasks] [] (Tasks.after c id deps)

/-- A step that reads task `id` alone (`priority`, `renew`). -/
def one (id : Int) (f : Db → Db × α) : Txn α := Txn.update [task id] [] f

/-- `task done`, the task out of the queue: the task, the communicator, the agent and what `staffing` reads. -/
def done (c : Ctx) (id : Int) (evidence : String) : Txn (Except String DoneOut) := do
  let ps ← poolSels
  Txn.update ([task id, Sels.metas ["comms"], Sels.agent c.me, Sels.parented] ++ ps) [] (Queue.done c id evidence)

/-- `task land`: the task and the lander's row, for its message. -/
def land (c : Ctx) (id : Int) (sha : String) (lander : Option String) : Txn (Except String Unit) :=
  Txn.update ([task id] ++ agents [lander.map strip]) [.msg] (Tasks.land c id sha lander)

/-- `task unland`: the task, the communicator, the lander's role and the former owner's row. -/
def unland (c : Ctx) (id : Int) (why : String) : Txn (Except String Unlanded) :=
  onTask id [.msg] (fun r => pure ([Sels.metas ["comms"]] ++ agents [some c.me, r.owner])) (Tasks.unland c id why)

/-- `task block`: the task and the away flag. -/
def block (c : Ctx) (id : Int) (q : String) : Txn (Except String Bool) :=
  Txn.update [task id, Sels.metas ["away"]] [] (Tasks.block c id q)

/-- `task unblock`: the task and the communicator. -/
def unblock (c : Ctx) (id : Int) (answer : String) : Txn (Except String (Option String)) :=
  Txn.update [task id, Sels.metas ["comms"]] [.msg] (Tasks.unblock c id answer)

/-- `task release`: the task, the communicator and, with `--after`, every task the new deps reach. -/
def release (c : Ctx) (id : Int) (af : Option (List Int)) : Txn (Except String (Option String)) := do
  let ids ← match af with
    | some l => closure l
    | none => pure []
  Txn.update [task id, Sels.metas ["comms"], tasks ids, allTasks] [.msg] (Tasks.release c id af)

/-- `task edit` (and `label`): the task and its owner's row. -/
def edit (c : Ctx) (id : Int) (a : EditArgs) : Txn (Except String (List String × Status)) :=
  onTask id [.msg] (fun r => pure (agents [r.owner])) (Tasks.edit c id a)

/-- `task drop`, its place gone: the task, the original it duplicates, the communicator, the agent's role, the waiters
and the places. -/
def drop (c : Ctx) (id : Int) (dup : Option Int) (note : Option String) : Txn (Except String (List Task)) :=
  Txn.update [task id, tasks dup.toList, Sels.metas ["comms"], Sels.agent c.me, waitingSel, queuedSel, undoneSel, Sels.parented] []
    (Queue.drop c id dup note)

/-- What `task show` reads: the task, its events, its deps and its waiters, and every task (its sub-issue tree, its
ancestors and their progress). -/
def showTxn (id : Int) : Txn Db := do
  let s ← Txn.slice [task id]
  let deps := ((s.find id).map depsOf).getD []
  Txn.slice [task id, evs id, tasks deps, waitingSel, queuedSel, allTasks]

/-- `task parent`: every task (the cycle check walks the tree). -/
def parent (c : Ctx) (id : Int) (p : Option Int) : Txn (Except String Unit) :=
  Txn.update [allTasks] [] (Tasks.setParent c id p)

/-- What `queue add` and `queue rm` read: the tasks named, the places and the communicator. -/
def queueSels (ids : List Int) : List Sel := [tasks ids, queuedSel, Sels.metas ["comms"]]

/-- `queue add`. -/
def qadd (c : Ctx) (ids : List Int) (w : Queue.Place) : Txn (Except String Unit) :=
  Txn.update (queueSels ids) [] (Queue.add c ids w)

/-- `queue rm`. -/
def qrm (c : Ctx) (ids : List Int) : Txn (Except String Unit) :=
  Txn.update (queueSels ids) [] (Queue.rm c ids)

/-- What `swarm queue` reads: the places and what `whyNot` reads. -/
def queueView : Txn Db := do
  let ps ← poolSels
  Txn.slice ps

/-- What `swarm board` reads: every task, the live agents and the staffing knobs. -/
def boardSels : List Sel :=
  [allTasks, { table := .agent, cond := .null "ended" },
   Sels.metas ["comms", "agent_min", "agent_max", "spawn_held"]]

/-- What `task backlog`, `task ready` and `task assign` read: the task, the places and the communicator. -/
def moveSels (id : Int) : List Sel := [task id, queuedSel, Sels.metas ["comms"]]

/-- `task backlog`. -/
def backlog (c : Ctx) (id : Int) (note : String) : Txn (Except String Unit) :=
  Txn.update (moveSels id) [] (Queue.backlog c id note)

/-- `task ready`. -/
def ready (c : Ctx) (id : Int) : Txn (Except String Unit) :=
  Txn.update (moveSels id) [] (Queue.ready c id)

/-- `task assign`. -/
def assign (c : Ctx) (id : Int) (who : Option String) : Txn (Except String Unit) :=
  Txn.update (moveSels id) [] (Queue.assign c id who)

/-- `rules set`: the communicator and the rules. -/
def setRules (c : Ctx) (text : String) : Txn (Except String Unit) :=
  Txn.update [Sels.metas ["comms", "rules"]] [] (Tasks.setRules c text)

end SwarmLean.TaskTxn
