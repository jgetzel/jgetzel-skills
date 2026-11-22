import SwarmLean.Db.Txn

namespace SwarmLean

/-- The database as the commands see it: a store that runs a function of the db as one transaction, given the tables
the function reads (`txn`, the whole-table store the unconverted commands use), or a `Txn`: keyed reads, a pure
decision on the rows read, its plan of statements (`run`, sw-global §3); or reads alone, the slice the selects pick
(`view`), which writes nothing. -/
class Store (m : Type → Type) where
  txn {α : Type} : List Table → (Db → Db × α) → m α
  run {α : Type} : Txn α → m α
  view {α : Type} : List Sel → (Db → α) → m α

/-- What a command's transactions see of the machine's db: one swarm's agents, knobs and events, and one repo's locks,
CI runs and worktrees. Swarm `''` is a repo's own (watchd's per-repo loop): its knobs at meta scope `repo:<path>`, its
events those of no swarm in that repo. `every`: the agents of every swarm. -/
structure Scope where
  swarm : String
  repo : String
  every : Bool := false

/-- The meta scope of a scope's own keys: its swarm, or `repo:<path>` for a repo's own. -/
def Scope.metaName (sc : Scope) : String := if sc.swarm == "" then "repo:" ++ sc.repo else sc.swarm

/-- Running in another scope: the store's and the working directory's (sw-global §4, watchd's loops over the swarms
and repos of the machine). -/
class Scoped (m : Type → Type) where
  /-- `x` with the store on scope `sc` and, when `sc.repo` is a folder, the working directory there; both back after. -/
  within {α : Type} : Scope → m α → m α

/-- Applies `step` to each request in turn from `db`: the db left and each request with its answer. -/
def replay (step : τ → Db → Db × α) : Db → List τ → Db × List (τ × α)
  | db, [] => (db, [])
  | db, x :: xs =>
    let (db', a) := step x db
    let (d, l) := replay step db' xs
    (d, (x, a) :: l)

end SwarmLean
