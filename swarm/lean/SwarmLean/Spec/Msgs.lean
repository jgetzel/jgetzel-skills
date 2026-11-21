import SwarmLean.Spec.Data

/-! The spec layer's messages (board #216): which messages are for an agent, the message transactions as data and S4's
invariant, moved from `Proofs/Msgs.lean`. -/

namespace SwarmLean.Inbox
open Msgs

/-- Message `r` is for agent `n`: from another sender, to `n` or to all. -/
def ToIt (n : String) (r : Msg) : Prop :=
  r.frm ≠ none ∧ r.frm ≠ some n ∧ (r.dest = some n ∨ r.dest = some "@all")

instance (n : String) : DecidablePred (ToIt n) := fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The messages for `n` with ids past cursor `a` up to cursor `b`, in log order. -/
def window (db : Db) (n : String) (a b : Int) : List Msg :=
  db.msgs.filter fun r => decide (ToIt n r ∧ a < r.id ∧ r.id ≤ b)

/-- The message log's invariant: ids increase along the log and stay below the next id, and so does every cursor; the
next id is positive. -/
def MInv (db : Db) : Prop :=
  (db.msgs.map (·.id)).Pairwise (· < ·) ∧ (∀ r ∈ db.msgs, r.id < db.msgNext) ∧ (∀ n, cursorOf db n < db.msgNext) ∧
    0 < db.msgNext

/-- `db'` only adds to `db`'s messages and cursors: messages after the old ones with fresh ids in order, and cursors
of agents that had none. -/
def Grows (db db' : Db) : Prop :=
  db.msgNext ≤ db'.msgNext ∧
  (∃ new, db'.msgs = db.msgs ++ new ∧ (new.map (·.id)).Pairwise (· < ·) ∧
    ∀ r ∈ new, db.msgNext ≤ r.id ∧ r.id < db'.msgNext) ∧
  ∃ more, db'.cursors = db.cursors ++ more ∧ ∀ c ∈ more, db.cursor c.agent = none ∧ c.last_msg_id.getD 0 < db'.msgNext

/-- A transaction the theorems cover: a post, `swarm read`, a delivery with a budget, or any other step that only grows
the messages and cursors of a db that keeps the invariant. -/
inductive MCmd
  | post (now : Int) (frm dest body : String) (urgent : Bool) (kind : Option String)
  | read (n : String)
  | deliver (n : String) (budget : Nat)
  | typed (n : String) (i : Nat)
  | other (f : Db → Db) (h : ∀ db, MInv db → Grows db (f db))

/-- Whom a transaction delivers to. -/
def MCmd.to : MCmd → Option String
  | .read n | .deliver n _ | .typed n _ => some n
  | _ => none

/-- What the deliveries to `n` among `t` showed, in order. -/
def shownTo (n : String) (t : List (MCmd × List Msg)) : List Msg :=
  t.flatMap fun (c, fit) => if c.to = some n then fit else []

/-- The message `post` appends. -/
def posted (db : Db) (now : Int) (frm dest body : String) (urgent : Bool) (kind : Option String) : Msg :=
  { id := db.msgNext, ts := some now, frm := some frm, dest := some dest, body := some body,
    urgent := some (if urgent then 1 else 0), kind := some (kind.getD (if dest == "@all" then "all" else "dm")) }

/-- An urgent row. -/
def Urgent (r : Msg) : Prop := r.urgent.getD 0 ≠ 0

/-- A row the waiter wakes on: anything but a notice, and an urgent notice. -/
def Wakes (r : Msg) : Prop := r.kind ≠ some "notice" ∨ Urgent r

instance : DecidablePred Urgent := fun _ => inferInstanceAs (Decidable (_ ≠ _))
instance : DecidablePred Wakes := fun _ => inferInstanceAs (Decidable (_ ∨ _))

end SwarmLean.Inbox
