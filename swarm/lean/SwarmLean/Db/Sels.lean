import SwarmLean.Db.Txn

/-! The keyed reads the converted commands make (sw-global §3), each on an index of the schema, and the step on one
agent's row that `touch` and `set_status` take. -/

namespace SwarmLean.Sels
open Sqlite (Val)

/-- Agent `n`'s row. -/
def agent (n : String) : Sel := { table := .agent, cond := .eq "name" (.text n) }

/-- `n`'s events of kind `k`. -/
def evOf (n k : String) : Cond := .and (.eq "agent" (.text n)) (.eq "kind" (.text k))

/-- `n`'s last event of kind `k` matching `c` too. -/
def lastEv (n k : String) (c : Cond := .all) : Sel := { table := .event, cond := .and (evOf n k) c, last := some 1 }

/-- The meta rows of keys `ks`. -/
def metas (ks : List String) : Sel := { table := .«meta», cond := .oneOf "k" (ks.map .text) }

/-- `n`'s cursor. -/
def cursor (n : String) : Sel := { table := .cursor, cond := .eq "agent" (.text n) }

/-- The tasks `n` owns. -/
def owned (n : String) : Sel := { table := .task, cond := .eq "owner" (.text n) }

/-- The locks `n` holds. -/
def locks (n : String) : Sel := { table := .lock, cond := .eq "agent" (.text n) }

/-- The worktrees recorded for `n`. -/
def workspaces (n : String) : Sel := { table := .workspace, cond := .eq "agent" (.text n) }

/-- What `Agents.fence` reads of `n`: its row and the last event that ended it. -/
def fence (n : String) : List Sel :=
  [agent n, { table := .event, cond := .and (.eq "agent" (.text n)) (.oneOf "kind" [.text "reap", .text "leave", .text "end"]),
              last := some 1 }]

/-- What `Agents.touch` reads of `n`: the fence's reads and its cursor. -/
def touch (n : String) : List Sel := fence n ++ [cursor n]

/-- A step on agent `n`'s row, its fence and its cursor (`touch`, `set_status`): the next message id is read only when
the row is missing, for the cursor touch makes then. -/
def onAgent (n : String) (f : Db → Db × α) : Txn α := do
  let d ← Txn.slice (touch n)
  let d ← if (d.agent n).isSome then pure d else Txn.slice (touch n) [.msg]
  let (d', a) := f d
  Txn.exec (slicePlan d d')
  pure a

end SwarmLean.Sels
