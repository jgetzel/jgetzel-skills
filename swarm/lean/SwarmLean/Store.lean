import SwarmLean.Db

namespace SwarmLean

/-- The outside world the commands are written against: a store that runs a function of the db as one transaction. -/
class Store (m : Type → Type) where
  txn {α : Type} : (Db → Db × α) → m α

/-- Runs a command against a store. -/
def exec [Store m] (c : Cmd) : m Result := Store.txn c.step

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

/-- The real store's transaction: an exclusive flock on `path.lock` held across reading `path`, applying `f`, and
writing the result to a temp file renamed over `path`. -/
def fileTxn (path : System.FilePath) (f : Db → Db × α) : IO α := do
  let lock ← IO.FS.Handle.mk (path.toString ++ ".lock") .append
  lock.lock
  try
    let db ← if ← path.pathExists then IO.ofExcept (Db.decode (← IO.FS.readFile path)) else pure {}
    let (db', a) := f db
    if db' ≠ db then
      -- shortcut: no fsync before the rename, so a power loss may lose the last write; add one if this becomes real.
      let tmp := s!"{path}.tmp{← IO.Process.getPID}"
      IO.FS.writeFile tmp db'.encode
      IO.FS.rename tmp path
    pure a
  finally lock.unlock

/-- The real store: the file at the path the reader holds. -/
instance : Store (ReaderT System.FilePath IO) where
  txn f := do fileTxn (← read) f

end SwarmLean
