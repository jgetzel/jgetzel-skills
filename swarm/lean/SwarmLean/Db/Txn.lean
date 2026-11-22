import SwarmLean.Db.Plan

/-! The statement store's transactions as data (sw-global §3): keyed or filtered reads into a slice of the db, a pure
decision on the slice, and a plan of `Stmt`s, plus a guarded update whose `changes()` the decision sees. Real.lean
runs a `Txn` in one BEGIN IMMEDIATE; `Txn.onDb` is what it does to the model `Db`, which `RecM`'s store runs. -/

namespace SwarmLean
open Sqlite (Val)

/-- A where clause as data: what a read selects, or what a guarded update also requires. -/
inductive Cond
  /-- every row -/
  | all
  /-- column `c` holds `v` -/
  | eq (c : String) (v : Val)
  /-- column `c` holds a value other than `v` (neither NULL) -/
  | ne (c : String) (v : Val)
  /-- column `c` holds a value above `v` (neither NULL) -/
  | gt (c : String) (v : Val)
  /-- column `c` is NULL -/
  | null (c : String)
  /-- column `c` is not NULL -/
  | notNull (c : String)
  /-- column `c` holds one of `vs` -/
  | oneOf (c : String) (vs : List Val)
  /-- column `c` holds a text that starts with `p` -/
  | pre (c : String) (p : String)
  /-- column `c` holds a text that contains `s` -/
  | has (c : String) (s : String)
  | and (a b : Cond)
  | or (a b : Cond)
  deriving Inhabited

/-- The clause's SQL and its parameters. -/
def Cond.sql : Cond → String × List Val
  | .all => ("1", [])
  | .eq c v => (s!"{c}=?", [v])
  | .ne c v => (s!"{c}<>?", [v])
  | .gt c v => (s!"{c}>?", [v])
  | .null c => (s!"{c} is null", [])
  | .notNull c => (s!"{c} is not null", [])
  | .oneOf c vs => if vs.isEmpty then ("0", []) else (s!"{c} in ({", ".intercalate (vs.map fun _ => "?")})", vs)
  | .pre c p => (s!"typeof({c})='text' and substr({c},1,{p.length})=?", [.text p])
  | .has c s => (s!"typeof({c})='text' and instr({c},?)>0", [.text s])
  | .and a b => let (x, p) := a.sql; let (y, q) := b.sql; (s!"({x}) and ({y})", p ++ q)
  | .or a b => let (x, p) := a.sql; let (y, q) := b.sql; (s!"({x}) or ({y})", p ++ q)

/-- Whether a cell is SQL's NULL. -/
def Sqlite.Val.isNull : Val → Bool
  | .null => true
  | _ => false

/-- Whether the clause holds of a row whose column `c` holds `cell c`: as SQLite compares cells of one type (the
order of `Val.ord`; a NULL compares to nothing). -/
def Cond.holds (cell : String → Val) : Cond → Bool
  | .all => true
  | .eq c v => !v.isNull && !(cell c).isNull && (cell c).ord == v.ord
  | .ne c v => !v.isNull && !(cell c).isNull && (cell c).ord != v.ord
  | .gt c v => !v.isNull && !(cell c).isNull && decide (v.ord < (cell c).ord)
  | .null c => (cell c).isNull
  | .notNull c => !(cell c).isNull
  | .oneOf c vs => vs.any fun v => !v.isNull && !(cell c).isNull && (cell c).ord == v.ord
  | .pre c p => match cell c with
    | .text s => s.startsWith p
    | _ => false
  | .has c s => match cell c with
    | .text t => s.isEmpty || (t.splitOn s).length > 1
    | _ => false
  | .and a b => a.holds cell && b.holds cell
  | .or a b => a.holds cell || b.holds cell

/-- The cell of column `c` in a row of type `α`; NULL for a column it lacks. -/
def Row.cell [Row α] (r : α) (c : String) : Val :=
  ((Row.cols α).zip (Row.enc r)).lookup c |>.getD .null

/-- A read of one table: the rows `cond` selects, or with `last` only the last that many of them by key. The real
store reads a swarm's agents and events and a repo's CI runs and worktrees (`inScope`); else the machine's (agent
names are the machine's, and a lock holds for every swarm in its repo). Locks are the machine's: a lock row carries its
repo, and a select of them names it. -/
structure Sel where
  table : Table
  cond : Cond := .all
  last : Option Nat := none
  inScope : Bool := true

/-- The rows of `rs` (in key order) that one select picks. -/
def Sel.pick [Row α] (s : Sel) (rs : List α) : List α :=
  let r := rs.filter fun x => s.cond.holds (Row.cell x)
  match s.last with
  | some n => r.drop (r.length - n)
  | none => r

/-- The rows of `rs` that any of the selects of table `t` picks, in key order. -/
def Sel.union [Row α] (t : Table) (ss : List Sel) (rs : List α) : List α :=
  let ss := ss.filter (·.table == t)
  if ss.isEmpty then [] else
  let keys := ss.flatMap fun s => (s.pick rs).map Row.key
  rs.filter fun x => keys.contains (Row.key x)

/-- The slice of `db` the selects `ss` read, with the next ids of the tables `next` (the others 0). -/
def Db.slice (db : Db) (ss : List Sel) (next : List Table) : Db where
  agents := Sel.union .agent ss db.agents
  msgs := Sel.union .msg ss db.msgs
  cursors := Sel.union .cursor ss db.cursors
  tasks := Sel.union .task ss db.tasks
  locks := Sel.union .lock ss db.locks
  conflicts := Sel.union .conflict ss db.conflicts
  pairkeys := Sel.union .pairkey ss db.pairkeys
  metas := Sel.union .«meta» ss db.metas
  events := Sel.union .event ss db.events
  workspaces := Sel.union .workspace ss db.workspaces
  cis := Sel.union .ci ss db.cis
  taskNext := if next.contains .task then db.taskNext else 0
  msgNext := if next.contains .msg then db.msgNext else 0
  eventNext := if next.contains .event then db.eventNext else 0
  swarm := db.swarm

/-- A transaction: reads, then what to do on the rows read. The continuations are pure: a decision on a slice. -/
inductive Txn (α : Type) where
  /-- the answer -/
  | done (a : α)
  /-- read the slice the selects pick (with the next ids of `next`), and go on with it -/
  | read (ss : List Sel) (next : List Table) (k : Db → Txn α)
  /-- run the statements, and go on -/
  | write (p : List Stmt) (k : Txn α)
  /-- run update or delete `s` only where `c` also holds, and go on with whether it changed a row (`changes()`) -/
  | guard (s : Stmt) (c : Cond) (k : Bool → Txn α)

/-- Sequencing: `t`, then `f` on its answer. -/
def Txn.bind : Txn α → (α → Txn β) → Txn β
  | .done a, f => f a
  | .read ss n k, f => .read ss n fun d => (k d).bind f
  | .write p k, f => .write p (k.bind f)
  | .guard s c k, f => .guard s c fun b => (k b).bind f

instance : Monad Txn where
  pure := .done
  bind := Txn.bind

/-- The slice the selects pick, with the next ids of `next`. -/
def Txn.slice (ss : List Sel) (next : List Table := []) : Txn Db := .read ss next .done

/-- Runs the statements. -/
def Txn.exec (p : List Stmt) : Txn Unit := .write p (.done ())

/-- Whether guarded statement `s` changed a row. -/
def Txn.guarded (s : Stmt) (c : Cond) : Txn Bool := .guard s c .done

/-- The plain shape: reads, a pure decision on the slice, its plan. -/
def Txn.step (ss : List Sel) (next : List Table) (decide : Db → List Stmt × α) : Txn α :=
  .read ss next fun d => let (p, a) := decide d; .write p (.done a)

/-- An event appended: an insert into `event` (its id the table's next), never a read of it. -/
def logStmt (ts : Int) (agent : Option String) (kind : String) (path data : Option String) : Stmt :=
  .ins "event" ["ts", "agent", "kind", "path", "data"] [.int ts, oS agent, .text kind, oS path, oS data]

/-- A row's insert. -/
def Row.ins [Row α] (r : α) : Stmt := .ins (Row.table α) (Row.cols α) (Row.enc r)

/-- A row's update by its key: every other column. -/
def Row.put [Row α] (r : α) : Stmt :=
  let n := Row.nkey α
  .upd (Row.table α) ((Row.cols α).take n) ((Row.enc r).take n) ((Row.cols α).drop n) ((Row.enc r).drop n)

/-- The plan that turns slice `s` into `s'`, a decision's new slice: per table the rows changed, added or gone
(`rowsPlan`), except that the events `s'` appended are inserts that leave their id to the table. -/
def slicePlan (s s' : Db) : List Stmt :=
  let evs := (s'.events.drop s.events.length).map fun e =>
    logStmt (e.ts.getD 0) e.agent (e.kind.getD "") e.path e.data
  rowsPlan s.agents s'.agents ++ rowsPlan s.msgs s'.msgs ++ rowsPlan s.cursors s'.cursors ++
  rowsPlan s.tasks s'.tasks ++ rowsPlan s.locks s'.locks ++ rowsPlan s.conflicts s'.conflicts ++
  rowsPlan s.pairkeys s'.pairkeys ++ rowsPlan s.metas s'.metas ++ evs ++
  rowsPlan s.workspaces s'.workspaces ++ rowsPlan s.cis s'.cis

/-- A step of the old shape (`Db → Db × α`) run on a slice: its plan is the slice's difference (`slicePlan`). For a
step that reads only what the selects pick. -/
def Txn.update (ss : List Sel) (next : List Table) (f : Db → Db × α) : Txn α :=
  .step ss next fun d => let (d', a) := f d; (slicePlan d d', a)

/-! ## The model: what a statement does to a `Db` -/

/-- Whether row `r` has the cells `k` in key columns `ks`. -/
def Row.atKey [Row α] (ks : List String) (k : List Val) (r : α) : Bool :=
  ks.length == k.length && (ks.zip k).all fun (c, v) => (Row.cell r c).ord == v.ord

/-- A row with columns `cs` set to `vs`, if it still decodes. -/
def Row.setCells [Row α] (cs : List String) (vs : List Val) (r : α) : Option α :=
  let cells := (Row.cols α).map fun c => ((cs.zip vs).lookup c).getD (Row.cell r c)
  (Row.dec cells.toArray).toOption

/-- The rows after statement `st` where `c` also holds, and how many it changed; `fresh` is the id an insert without
one gets. A statement on another table, or a row that would not decode, leaves them as they were. -/
def Row.execIf [Row α] (st : Stmt) (c : Cond) (fresh : Nat) (rs : List α) : List α × Nat :=
  let hit (ks : List String) (k : List Val) (r : α) := Row.atKey ks k r && c.holds (Row.cell r)
  match st with
  | .del t ks k => if t != Row.table α then (rs, 0) else
    let n := (rs.filter (hit ks k)).length
    (rs.filter fun r => !hit ks k r, n)
  | .upd t ks k cs vs => if t != Row.table α then (rs, 0) else
    ((rs.map fun r => if hit ks k r then (Row.setCells cs vs r).getD r else r), (rs.filter (hit ks k)).length)
  | .ins t cs vs => if t != Row.table α then (rs, 0) else
    let cells := (Row.cols α).map fun col => ((cs.zip vs).lookup col).getD (if col == "id" then .int fresh else .null)
    match (Row.dec cells.toArray).toOption with
    | some r => (sortRows (rs ++ [r]), 1)
    | none => (rs, 0)
  | _ => (rs, 0)

/-- `db` after statement `st` where `c` also holds, and how many rows it changed. An insert with no id takes the
table's next. -/
def Db.execIf (st : Stmt) (c : Cond) (db : Db) : Db × Nat :=
  let noId := match st with | .ins _ cs _ => !cs.contains "id" | _ => false
  let bump (n next : Nat) := if noId && n > 0 then next + 1 else next
  let (agents, a) := Row.execIf st c 0 db.agents
  let (msgs, m) := Row.execIf st c db.msgNext db.msgs
  let (cursors, cu) := Row.execIf st c 0 db.cursors
  let (tasks, t) := Row.execIf st c db.taskNext db.tasks
  let (locks, l) := Row.execIf st c 0 db.locks
  let (conflicts, co) := Row.execIf st c 0 db.conflicts
  let (pairkeys, p) := Row.execIf st c 0 db.pairkeys
  let (metas, me) := Row.execIf st c 0 db.metas
  let (events, e) := Row.execIf st c db.eventNext db.events
  let (workspaces, w) := Row.execIf st c 0 db.workspaces
  let (cis, ci) := Row.execIf st c 0 db.cis
  ({ agents, msgs, cursors, tasks, locks, conflicts, pairkeys, metas, events, workspaces, cis
     taskNext := bump t db.taskNext, msgNext := bump m db.msgNext, eventNext := bump e db.eventNext, swarm := db.swarm },
   a + m + cu + t + l + co + p + me + e + w + ci)

/-- A transaction run on the model db: the db it leaves and its answer. -/
def Txn.onDb : Txn α → Db → Db × α
  | .done a, db => (db, a)
  | .read ss n k, db => (k (db.slice ss n)).onDb db
  | .write p k, db => k.onDb (p.foldl (fun d s => (Db.execIf s .all d).1) db)
  | .guard s c k, db => let (d, n) := Db.execIf s c db; (k (n > 0)).onDb d

end SwarmLean
