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

/-- The messages to `dests` past id `c` that `n` did not send: an inbox, on index msg(dest, id). -/
def inbox (n : String) (dests : List String) (c : Int) : Sel :=
  { table := .msg, cond := .and (.and (.oneOf "dest" (dests.map .text)) (.gt "id" (.int c))) (.ne "frm" (.text n)) }

/-- Task `id`. -/
def task (id : Int) : Sel := { table := .task, cond := .eq "id" (.int id) }

/-- The tasks `n` owns. -/
def owned (n : String) : Sel := { table := .task, cond := .eq "owner" (.text n) }

/-- The locks `n` holds. -/
def locks (n : String) : Sel := { table := .lock, cond := .eq "agent" (.text n) }

/-- The worktrees recorded for `n`. -/
def workspaces (n : String) : Sel := { table := .workspace, cond := .eq "agent" (.text n) }

/-- Every row of table `t` in scope. -/
def all (t : Table) : Sel := { table := t }

/-- The job-start and job-end events (`Run.liveJobs`): never the rest of the event table. -/
def jobs : Sel := { table := .event, cond := .oneOf "kind" [.text "job-start", .text "job-end"] }

/-- Job `j`'s job-end, if logged. -/
def jobEnd (j : Option String) : Sel :=
  { table := .event, cond := .and (.eq "kind" (.text "job-end")) (match j with | some p => .eq "path" (.text p) | none => .null "path") }

/-- The meta rows whose key starts with `p`. -/
def metaPre (p : String) : Sel := { table := .«meta», cond := .pre "k" p }

/-- The worktree row `(path, agent)`. -/
def workspace (path agent : String) : Sel :=
  { table := .workspace, cond := .and (.eq "path" (.text path)) (.eq "agent" (.text agent)) }

/-- The scope's live agents. -/
def live : Sel := { table := .agent, cond := .null "ended" }

/-- The conflicts naming `n`. -/
def conflicts (n : String) : Sel := { table := .conflict, cond := .or (.eq "a" (.text n)) (.eq "b" (.text n)) }

/-- The pair keys naming `n`. -/
def pairkeys (n : String) : Sel := { table := .pairkey, cond := .or (.eq "a" (.text n)) (.eq "b" (.text n)) }

/-- What `Agents.release` and `Agents.endRow` read of `n`: its row, the tasks it owns, its locks, conflicts and pair keys. -/
def release (n : String) : List Sel := [agent n, owned n, locks n, conflicts n, pairkeys n]

/-- The staffing knobs `Agents.limits` and `limitsLine` read, and the communicator. -/
def LIMIT_KEYS : List String := ["comms", "agent_min", "agent_max", "queue_only"]

/-- What `Agents.limits` reads: the live agents and the staffing knobs. -/
def limits : List Sel := [live, metas LIMIT_KEYS]

/-- Task `i`'s row. -/
def task (i : Int) : Sel := { table := .task, cond := .eq "id" (.int i) }

/-- The tasks of ids `is`. -/
def tasks (is : List Int) : Sel := { table := .task, cond := .oneOf "id" (is.map .int) }

/-- The cursors of agents `ns`. -/
def cursors (ns : List String) : Sel := { table := .cursor, cond := .oneOf "agent" (ns.map .text) }

/-- The messages to `n` past cursor `cur`: a task box's held notes (`#N`; a swarm's `@<swarm>` is no box's). -/
def unreadPast (n : String) (cur : Int) : Sel :=
  { table := .msg, cond := .and (.gt "id" (.int cur)) (.eq "dest" (.text n)) }

/-- What `Agents.fence` reads of `n`: its row and the last event that ended it. -/
def fence (n : String) : List Sel :=
  [agent n, { table := .event, cond := .and (.eq "agent" (.text n)) (.oneOf "kind" [.text "reap", .text "leave", .text "end"]),
              last := some 1 }]

/-- What `Agents.touch` reads of `n`: the fence's reads and its cursor. -/
def touch (n : String) : List Sel := fence n ++ [cursor n]

/-- A step on agent `n`'s row, its fence and its cursor (`touch`, `set_status`), and what `extra` selects: the next
message id is read only when the row is missing, for the cursor touch makes then. -/
def onAgent (n : String) (f : Db → Db × α) (extra : List Sel := []) : Txn α := do
  let d ← Txn.slice (touch n ++ extra)
  let d ← if (d.agent n).isSome then pure d else Txn.slice (touch n ++ extra) [.msg]
  let (d', a) := f d
  Txn.exec (slicePlan d d')
  pure a

end SwarmLean.Sels
