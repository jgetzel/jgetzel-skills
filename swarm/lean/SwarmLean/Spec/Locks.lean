import SwarmLean.Spec.Board

/-! The spec layer's locks (board #216): the lock commands as data and S3's invariant, moved from `Proofs/Locks.lean`. -/

namespace SwarmLean.Locks
open Agents

/-- Agent `a` has a row that hasn't ended (the agent join of `others`). -/
def Live (db : Db) (a : String) : Bool := db.agents.any fun g => g.name == a && g.ended.isNone

/-- Lock `l` holds at time `t`: its agent is live and its lease runs past `t` (the locks `others` reads at `t`). -/
def HeldAt (db : Db) (t : Int) (l : Lock) : Prop :=
  ∃ a, l.agent = some a ∧ l.lease_until.any (· > t) = true ∧ Live db a = true

/-- S3 at time `t`: two locks of different agents that both hold at `t` don't overlap. -/
def Disjoint (db : Db) (t : Int) : Prop :=
  ∀ l ∈ db.locks, ∀ m ∈ db.locks, HeldAt db t l → HeldAt db t m → l.agent ≠ m.agent → overlaps l.path m.path = false

/-- Every lock's agent is live, or is the user (whom `touch` gives no row and `join` refuses). -/
def Rows (db : Db) : Prop := ∀ l ∈ db.locks, ∀ a, l.agent = some a → a = HUMAN ∨ Live db a = true

/-- The invariant at time `t`. -/
def Good (db : Db) (t : Int) : Prop := Rows db ∧ Disjoint db t

/-- A command the lock theorems cover: `swarm lock`, `unlock`, `leave`, `join`'s transaction (`r`, the row as it read
it before), or a task command of `Proofs.lean`. -/
inductive LCmd
  | lock (c : Tasks.Ctx) (path reason lease : String)
  | unlock (me path : String) (now : Int)
  | leave (name : String) (now : Int)
  | join (name : String) (cwd hc model : Option String) (r : Binding) (now : Int)
  | task (c : Cmd)

/-- What a lock command answers. -/
inductive LResult
  | locked (r : Except String Unit)
  | unlocked
  | left
  | joined (r : Except String Unit)
  | task (r : Result)

/-- The time `t` is no earlier than the clock each `swarm lock` among `cs` read: what a clock that never runs back
gives at any moment after they ran. -/
def Before (t : Int) (cs : List LCmd) : Prop := ∀ x ∈ cs, ∀ c p r l, x = .lock c p r l → c.now ≤ t

end SwarmLean.Locks
