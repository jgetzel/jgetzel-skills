import SwarmLean.Spec.Locks
import SwarmLean.Spec.Msgs

/-! The spec layer across areas (board #216): every transaction of the four areas as data and the cross-area invariant,
moved from `Proofs/Cross.lean`. -/

namespace SwarmLean.Cross
open Board Agents

/-- Every transaction the theorems of #103-#106 cover, of all four areas: the task commands, the message transactions,
the lock commands with leave and join, and watchd's end and reaps. -/
inductive XCmd
  | task (c : TCmd)
  | post (now : Int) (frm dest body : String) (urgent : Bool) (kind : Option String)
  | read (n : String)
  | deliver (n : String) (budget : Nat)
  | typed (n : String) (i : Nat)
  | lock (c : Locks.LCmd)
  | end_ (n : String) (hc : Option String) (force : Bool) (by_ : Option String) (now : Int)
  | reapTask (r : Task) (t now : Int)
  | reapLock (l : Lock) (t now : Int)
  | reapGone (n h : String) (t : Int)

/-- Every area's invariant at time `t`: the board's (ids, owners, S5), the inbox's (S4's) and the locks' (S3). -/
def XInv (db : Db) (t : Int) : Prop := BInv db ∧ Inbox.MInv db ∧ Locks.Good db t

/-- `t` is no earlier than the clock of each `swarm lock` among `cs` (`Locks.Before`). -/
def XBefore (t : Int) (cs : List XCmd) : Prop := ∀ x ∈ cs, ∀ c p r l, x = .lock (.lock c p r l) → c.now ≤ t

/-- Task `i` is claimed by `o` with lease `L`. -/
def ClaimedBy (db : Db) (i : Int) (o : String) (L : Int) : Prop :=
  ∃ u, db.find i = some u ∧ u.owner = some o ∧ u.status = .claimed ∧ u.lease_until = some L

/-- Row `a` is live and bound to terminal `h`. -/
def BoundLive (db : Db) (a h : String) : Prop := ∃ g, db.agent a = some g ∧ g.hc = some h ∧ g.ended = none

end SwarmLean.Cross
