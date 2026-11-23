import SwarmLean.Spec.Data

/-! The spec layer's tasks and queue (board #216): the task commands as data and the board's and the queue's invariants,
which the challenged theorems state (`Challenge.lean`). Moved from `Proofs.lean`, `Proofs/Tasks.lean` and
`Proofs/Queue.lean` under their own names; the commands' steps, which run the code, are in `Spec/Code.lean`. -/

namespace SwarmLean
open Tasks

/-- A command the theorems cover, with everything it reads of the world. -/
inductive Cmd
  | add (c : Tasks.Ctx) (a : AddArgs)
  | claim (c : Tasks.Ctx) (i : Int) (lease : String)
  | release (c : Tasks.Ctx) (i : Int) (after : Option (List Int))
  | land (c : Tasks.Ctx) (i : Int) (sha : String) (lander : Option String)
  | unland (c : Tasks.Ctx) (i : Int) (why : String)
  | board

/-- What a command answers. -/
inductive Result
  | added (r : Except String Nat)
  | claimed (r : Except String Claimed)
  | released (r : Except String (Option String))
  | landed (r : Except String Unit)
  | unlanded (r : Except String Unlanded)
  | board (tasks : List Task)

/-- A task's owner fits its state: a claimed task has an owner, an open one has none. It holds of every task by
construction (`TaskState.owned`): the owner is the state's (`TaskState.claimed` holds one, `.open` none). -/
def Task.Owned (t : Task) : Prop :=
  (t.status = .claimed → t.owner.isSome) ∧ (t.status = .open → t.owner = none)

/-- The store's invariant: task ids are unique and below the next id, and every task's owner fits its state. -/
def Inv (db : Db) : Prop :=
  (db.tasks.map (·.id)).Nodup ∧ (∀ t ∈ db.tasks, t.id < db.taskNext) ∧ ∀ t ∈ db.tasks, t.Owned

/-- Agent `a` owns task `i` in `db`. -/
def Owns (db : Db) (i : Int) (a : String) : Prop := ∃ t ∈ db.tasks, (t.id : Int) = i ∧ t.owner = some a

end SwarmLean

namespace SwarmLean.Board
open Tasks

/-- Every task command, with everything it reads of the world. -/
inductive TCmd
  | add (c : Ctx) (a : AddArgs)
  | claim (c : Ctx) (i : Int) (lease : String)
  | after (c : Ctx) (i : Int) (deps : List Int)
  | priority (c : Ctx) (i : Int) (p : Int)
  | renew (c : Ctx) (i : Int) (lease : String)
  | done (c : Ctx) (i : Int) (evidence : String)
  | block (c : Ctx) (i : Int) (question : String)
  | unblock (c : Ctx) (i : Int) (answer : String)
  | release (c : Ctx) (i : Int) (after : Option (List Int))
  | edit (c : Ctx) (i : Int) (a : EditArgs)
  | drop (c : Ctx) (i : Int)
  | land (c : Ctx) (i : Int) (sha : String) (lander : Option String)
  | unland (c : Ctx) (i : Int) (why : String)
  | board

/-- Evidence `task done` accepts: some text that is not all whitespace. -/
def EvOk (e : Option String) : Prop := ∃ s, e = some s ∧ strip s ≠ ""

/-- S5 of one task: if it is done it has evidence. An invariant, not the type's: evidence is a column, which a red task
keeps when its `task done` reopens it, and "not all whitespace" is no constructor's. -/
def DoneEv (t : Task) : Prop := t.status = .done → EvOk t.evidence

/-- The board's invariant: `Inv` (ids unique and below the next id, owners fit states) and every done task has
evidence. -/
def BInv (db : Db) : Prop := Inv db ∧ ∀ t ∈ db.tasks, DoneEv t

/-- A successful claim of task `i`. -/
def ClaimedOf (i : Int) : TCmd × Bool → Bool
  | (.claim _ j _, true) => j == i
  | _ => false

/-- A successful release of task `i`, or a successful done of it (a red task's done reopens it), or a successful
unland of it (its lander gives it back, open). -/
def ReleasedOf (i : Int) : TCmd × Bool → Bool
  | (.release _ j _, true) => j == i
  | (.done _ j _, true) => j == i
  | (.unland _ j _, true) => j == i
  | _ => false

/-- `t` waits on `x` in the pool's sense: `x`'s id is one of the ids in `t`'s deps text. -/
def WaitsOn (t x : Task) : Prop := ∃ ds, t.deps = some ds ∧ hasSub ("," ++ ds ++ ",") ("," ++ d x.id ++ ",") = true

end SwarmLean.Board

namespace SwarmLean.QueueProofs

/-- The places the queued tasks hold. -/
def places (db : Db) : List Int := db.tasks.filterMap (·.qpos)

/-- The queue's invariant: the queued tasks hold the places 1..n, each once. -/
def QInv (db : Db) : Prop := ∃ n, (places db).Perm ((List.range n).map fun (i : Nat) => (i : Int) + 1)

end SwarmLean.QueueProofs
