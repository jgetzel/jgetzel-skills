import SwarmLean.Db

namespace SwarmLean

/-- The database as the commands see it: a store that runs a function of the db as one transaction, given the tables
the function reads. -/
class Store (m : Type → Type) where
  txn {α : Type} : List Table → (Db → Db × α) → m α

/-- Applies `step` to each request in turn from `db`: the db left and each request with its answer. -/
def replay (step : τ → Db → Db × α) : Db → List τ → Db × List (τ × α)
  | db, [] => (db, [])
  | db, x :: xs =>
    let (db', a) := step x db
    let (d, l) := replay step db' xs
    (d, (x, a) :: l)

/-- What "the store is well behaved" means, assumed of the real store and not proved: when processes ran their
requests `ran` (each with the answer it got) at once on a store holding `before` and left `after`, the requests
applied one after another in some order give those answers and `after`. -/
def Atomic (step : τ → Db → Db × α) (before after : Db) (ran : List (τ × α)) : Prop :=
  ∃ order : List (τ × α), order.Perm ran ∧ replay step before (order.map (·.1)) = (after, order)

end SwarmLean
