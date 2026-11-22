# sw-global proofs: the statements, and the plan for #79-#82

Plan, 2026-11-21, against `origin/main` at 2ff8b35, which includes the statement store (board #69). The spec is
`sw-global.md` §3 "How the proofs work afterwards". This doc fixes the Lean statements: signatures only, no proofs.
§3's signatures were checked with `lake env lean` against stubs for what is not on main yet. Board tasks #79-#82 and
the prerequisite task #99 (§1) build them. Where a statement names something that is not on main yet, it says which task makes it.

## 0. What there is to build on

- **SQLite's meaning** (`Assumptions/Code.lean`): `STable`, `SDb`, `Stmt.run`, `Stmt.Pre`, `Sql`, and the assumptions
  `SqlExec`/`SqlSelect`/`SqlTableInfo`, which `swarm-tests`' `sqlite_spec` tests against real SQLite.
- **The statement store** (#69, `Db/Txn.lean`): `Cond` (a where clause as data) and `Cond.holds`; `Sel` (a select of
  one table, optionally the last n by key) and `Sel.pick`; `Db.slice`; `Txn`, a free monad of `read`/`write`/`guard`;
  `Txn.update ss next f`, which runs an old-shape step `f : Db → Db × α` on a slice and writes the slice's difference
  (`slicePlan`); `logStmt`, `Row.ins`, `Row.put`; and **the model of a statement on a `Db`**, `Db.execIf st c`, with
  `Txn.onDb`. `RecM`'s store runs a `Txn` as `Txn.onDb` and `Real.lean` runs it as `runTxnOn`. A `Sel` with
  `inScope := false` reads the machine's rows of its table, not the scope's. `sqlite_txn` checks the
  two against each other on real SQLite.
- **Scopes** (#68, moving into `Store.lean` in #75): a command's `Db` is **one scope's view** of the machine db: the
  agents, knobs and events of `sc.swarm`, the locks and CI runs of `sc.repo`, and every task, message, cursor, conflict
  and pairkey (`Real.loadDb`, `readSlice`). Writes get the scope's cells from `scopeStmt`/`scopeStmts`, which also map
  meta `comms` to `swarm.comms` and move an agent row on insert. `every` (#75) widens a view to every swarm's agents.
- **The old proofs** are all about `Db → Db × α` step functions and `replay`/`Atomic` over `Db`. #84 took them out of
  the build. Their invariants live in `Spec/*.lean`: `Board.BInv`, `QueueProofs.QInv`, `Inbox.MInv`, `Locks.Good`,
  `Cross.XInv`.

**The shape of the plan.** The old decision-level theorems stay as they are. They are about pure functions of a `Db`,
and those functions stay the decisions the converted commands run (or become their specs). What is new:

1. one link from SQLite to the model (`abs`, per-statement lemmas, reads, `Txn.onSql` refines `Txn.onDb`);
2. one bridge per command: its `Txn` refines its old step;
3. invariants of the machine db, stated through views (`WF`), and preserved by every command's transaction;
4. isolation, as a frame property of `scopeStmts`.

`abs` takes a scope, `abs sc : SDb → Db`, because the model `Db` is what one scope sees. Facts about the whole machine
(an agent's swarm, a lock's holder in another swarm) are stated by quantifying over views (§3.6). That avoids a second
model with its own statement semantics.

## 1. Findings that change the code before the proofs can be stated

1. **The machine tables are outside the store.** `Lib/Swarms.lean`, and #74's `task_repo` on its branch, read and write
   `swarm`, `repo`, `swarm_repo` and `task_repo` with raw `Sys.sqlAt`. In `RecM` that is an `Eff.sql` effect, so the
   model db never sees those rows, and none of WF's swarm and repo clauses can be proved. Worse, `task add` writes the
   task and its `task_repo` rows in two transactions. A crash between them leaves a task with no repo, and auto-spawn
   then never staffs it. **New task #99 (after #74, #77, before #79):**
   - put the four tables on `Db` as unscoped tables (every view sees them), with row types and `Table` constructors;
   - move every read and write of them onto `Store.run`/`Store.view`, with `task add` in one transaction;
   - move the scoping (`Scope`, a pure `scopeCond : Scope → Table → Cond`, `scopeStmt`, `scopeStmts`, meta `comms`) into
     a pure module `Db/Scope.lean` that `Real.lean`'s reads and writes call.

   The proofs can only name pure code, and `Real.lean` is IO.
2. **Locks across swarms.** `Locks.others` (so `swarm lock` and the edit hook's `lockHolder`) counts a lock as held
   only if `db.agents` has its live holder. Agents are read `where swarm=?`, so a live lock in repo R held by swarm S2
   reads as not held in swarm S1. S1 can then take an overlapping lock, or edit the locked file. #73's done-when already
   asks for cross-swarm refusal. The cause is the agents read, so the lock reads must see every swarm's agents (a keyed
   read of the holders' rows, or an `every` view). WF's lock clause (§3.6) reads every swarm's agents for this reason.
3. **The per-repo sweep must see every swarm's agents.** `Gate.unused` (sweep_W1) requires that no live agent's
   `wt`/`cwd` is inside the worktree. With one watchd per machine and a per-repo sweep, that has to be every swarm's
   agents, or the sweep could remove a worktree another swarm's agent works in. #75 already runs the sweep in an
   `every` scope (gl-4: `repoTick`, `repoScope`). #82 restates `Gate` over that view.
4. **`@all` now means the sender's swarm** (sw-global §2). `Inbox.ToIt` (`r.dest = some n ∨ r.dest = some "@all"`) and
   every exactly-once theorem read it. #71 should resolve `@all` purely in the post's decision, for example by
   rewriting it to `@<swarm>`. Then #81 can state `ToIt` with the addressee's swarm (§3.7).
5. **`Stmt.run` lacks three things the store now uses**: AUTOINCREMENT ids (`logStmt` and new tasks and messages insert
   without an id), the guarded update with `changes()`, and `select … where … [order by … desc limit n]`. #79 adds them
   to `Assumptions/Code.lean`, with `sqlite_spec` cases (`sqlite_txn` already covers what they say).
6. **`Atomic` and `replay` are over `Db`.** Concurrency is now machine-wide (other scopes' transactions interleave), so
   #79 generalises both to any state type. The old uses keep `σ := Db` and read the same.

## 2. Layers

```
SDb  ──abs sc──▶  Db (scope sc's view)  ──decision──▶  plan / answer
 ▲ Stmt.run, Stmt.runIf, selectWhere      ▲ Db.execIf, Db.slice, Txn.onDb
 └── Txn.onSql S sc  (mirrors Real.runTxnOn: readSlice + scopeStmts)
```

- **SQL**: SQLite's meaning (assumed, tested).
- **View**: what a command decides on. All old invariants are on it.
- **Machine**: `WF : SDb → Int → Prop`, a conjunction of view facts over all scopes.

Files: `Assumptions/Code.lean` (SQL additions), `Spec/Store.lean` (new: `abs`, `Good`, `WF`, `InScope`; imports no
proof and no implementation, so `Challenge.lean` can state through it), `Proofs/Abs.lean` (the lemmas of §3.1-§3.5),
`Proofs/Wf.lean` (§3.6-§3.8, generic). The per-family files of #80-#82 follow.

## 3. The statements

All in `namespace SwarmLean`. `S : Sql`. "`hS`" abbreviates `(hS : SqlExec S) (hI : SqlExecIf S) (hW : SqlSelectWhere S)`.

### 3.1 SQLite additions (`Assumptions/Code.lean`, #79)

```lean
structure STable where
  cols : List String
  keys : List String
  text : List String
  dflt : String → Sqlite.Val
  rows : List (String → Sqlite.Val)
  /-- the INTEGER PRIMARY KEY AUTOINCREMENT column, if the table has one -/
  auto : Option String := none
  /-- `sqlite_sequence.seq` of the table -/
  seq : Nat := 0

/-- The id an insert that names no id takes: one past the larger of `seq` and the largest id there. -/
def STable.nextId (T : STable) (c : String) : Nat

-- Stmt.run's `.ins` case, extended: when `T.auto = some c` and `c ∉ cs`, the row gets `c := .int (T.nextId c)` and
-- the table `seq := T.nextId c`. Every other case is unchanged.

/-- The table a statement names. -/
def Stmt.tbl : Stmt → String

/-- What SQLite does with update or delete `st` run as `… where <key> and (<c>)`, and `changes()`; none for any other
statement. -/
def Stmt.runIf (db : SDb) (st : Stmt) (c : Cond) : Option (SDb × Nat)

/-- Rows of `T` that `select … where c` picks, in key order; with `some n`, the last `n` of them (`order by <key> desc
limit n`, as `Real.selRows` asks). -/
def STable.pick (T : STable) (c : Cond) (n : Option Nat) : List (String → Sqlite.Val)

/-- The cells `c` compares are each NULL or of one class with what it is compared to (as `KeyClass` for keys), in
columns `T` has. -/
def CondClass (T : STable) (c : Cond) : Prop

structure Sql where
  exec : Stmt → SDb → Option SDb
  execIf : Stmt → Cond → SDb → Option (SDb × Nat)
  select : SDb → String → List String → List (Array Sqlite.Val)
  selectWhere : SDb → String → List String → Cond → Option Nat → List (Array Sqlite.Val)
  tableInfo : SDb → String → List String

/-- SQLite: a guarded update or delete takes the rows at the key where `c` also holds, and `changes()` counts them
(sqlite_spec: sqlite_txn). -/
def SqlExecIf (S : Sql) : Prop :=
  ∀ db st c, st.Pre db → CondClass (db st.tbl) c → S.execIf st c db = st.runIf db c

/-- SQLite: a select with a where clause (and a last-n limit) returns the rows `STable.pick` picks, in some order
(sqlite_spec: sqlite_txn). -/
def SqlSelectWhere (S : Sql) : Prop :=
  ∀ db t cs c n, (∀ x ∈ cs, x ∈ (db t).cols) → CondClass (db t) c →
    (S.selectWhere db t cs c n).Perm (((db t).pick c n).map fun r => (cs.map r).toArray)

theorem sql_consistent : SqlExec .model ∧ SqlExecIf .model ∧ SqlSelectWhere .model ∧ SqlSelect .model ∧
    SqlTableInfo .model

/-- `Atomic` over any state (finding 6): the old one is `AtomicOn (σ := Db)`. -/
def replayOn (step : τ → σ → σ × α) : σ → List τ → σ × List (τ × α)
def Atomic (step : τ → σ → σ × α) (before after : σ) (ran : List (τ × α)) : Prop :=
  ∃ order : List (τ × α), order.Perm ran ∧ replayOn step before (order.map (·.1)) = (after, order)
```

### 3.2 The abstraction (`Spec/Store.lean`, #79)

```lean
/-- The rows of table `t` in `d` that scope `sc` reads (`Db/Scope.lean`'s `scopeCond sc t`), decoded; a row that does
not decode is left out (`Good` says there is none). -/
def absRows [Row α] (sc : Scope) (t : Table) (d : SDb) : List α

/-- The machine db as scope `sc`'s commands see it: `Real.readSlice` of every row of every table, with the next ids
(`max seq maxid + 1`, as `Real.nextId`), and meta `comms` from `swarm.comms`. -/
def abs (sc : Scope) (d : SDb) : Db

/-- `abs sc d` with the tables in `wide` read machine-wide: what a transaction whose selects of those tables have
`inScope := false` reads (`Sel.inScope`, #69). `abs sc d = absW sc [] d`. -/
def absW (sc : Scope) (wide : List Table) (d : SDb) : Db

/-- The schema on a fresh db (`Db/Schema.lean`'s `schema`): each table's columns, keys, text columns, defaults and
AUTOINCREMENT column, no rows. A `sqlite_spec` case checks `pragma table_info` of each table against it. -/
def freshDb : SDb

/-- The SQL-level well-formedness: every table has `freshDb`'s columns and keys, every row decodes as its row type and
its cells fit their columns, keys are distinct and of their class, and `seq` is at least every id. -/
def Good (d : SDb) : Prop

/-- Every table of a view is in strictly increasing key order (so keys are unique). -/
def Keyed (db : Db) : Prop

/-- A table's name in the schema. -/
def Table.name : Table → String

/-- A table of `Db` as a list of its row type. Each instance's `set` changes its field alone: #79 states that as one
simp lemma per instance and field (`Tbl.set` of tasks keeps `agents`, …). -/
class Tbl (α : Type) [Row α] where
  table : Table
  name_eq : table.name = Row.table α
  get : Db → List α
  set : Db → List α → Db
  get_set : ∀ db l, get (set db l) = l

instance : Tbl Task
instance : Tbl Agent
instance : Tbl Msg
instance : Tbl Cursor
instance : Tbl Lock
instance : Tbl Conflict
instance : Tbl Pairkey
instance : Tbl Meta
instance : Tbl Event
instance : Tbl Workspace
instance : Tbl Ci
instance : Tbl SwarmRow
instance : Tbl RepoRow
instance : Tbl SwarmRepo
instance : Tbl TaskRepo
```

`abs` facts (`Proofs/Abs.lean`, #79):

```lean
theorem good_fresh : Good freshDb
theorem abs_fresh (sc : Scope) : abs sc freshDb = {}
theorem good_keyed (h : Good d) (sc : Scope) : Keyed (abs sc d)
/-- The unscoped tables are the same in every view. -/
theorem abs_shared (sc sc' : Scope) (d : SDb) :
    (abs sc d).tasks = (abs sc' d).tasks ∧ (abs sc d).msgs = (abs sc' d).msgs ∧
    (abs sc d).cursors = (abs sc' d).cursors ∧ (abs sc d).conflicts = (abs sc' d).conflicts ∧
    (abs sc d).pairkeys = (abs sc' d).pairkeys ∧ (abs sc d).swarms = (abs sc' d).swarms ∧
    (abs sc d).repos = (abs sc' d).repos ∧ (abs sc d).swarmRepos = (abs sc' d).swarmRepos ∧
    (abs sc d).taskRepos = (abs sc' d).taskRepos ∧ (abs sc d).taskNext = (abs sc' d).taskNext ∧
    (abs sc d).msgNext = (abs sc' d).msgNext ∧ (abs sc d).eventNext = (abs sc' d).eventNext
/-- Load after the migrations: `connect`'s `migs` change nothing on a fresh-schema db. -/
theorem migs_fresh (hS : SqlExec S) (hT : SqlTableInfo S) (h : Good d) : S.migrateAll migs d = some d
```

### 3.3 One lemma per statement kind

Two levels. The model level is about `Db.execIf` alone, so the decision proofs can use it. The SQL level gives the
spec's `abs (run (ins r) d) = (abs d).insert r` form. Below, `r : α` with `[Row α] [RowLaws α] [Tbl α]`, `db : Db`
with `Keyed db`, and "the table" is `Tbl.get db`.

```lean
/-- The rows of `l` whose key columns hold `k`. -/
def atKeyRows [Row α] (ks : List String) (k : List Sqlite.Val) (l : List α) : List α := l.filter (Row.atKey ks k)

-- ins: an insert adds the row, in key order (SQLite refuses a key that is there: `abs_run` holds only of a run that
-- went through); an id-less insert takes the table's next id
theorem execIf_ins :
    db.execIf (Row.ins r) .all = (Tbl.set db (sortRows (Tbl.get db ++ [r])), 1)
theorem execIf_log (h : ∀ e ∈ db.events, e.id < db.eventNext) (ts ag k p dt) :
    (db.execIf (logStmt ts ag k p dt) .all).1 = db.log ts ag k p dt

-- upd: an update maps the rows at the key (none, or the one there) and leaves every other table
theorem execIf_upd (ks : List String) (k : List Sqlite.Val) (cs : List String) (vs : List Sqlite.Val) :
    db.execIf (.upd (Row.table α) ks k cs vs) .all =
      (Tbl.set (α := α) db ((Tbl.get db : List α).map fun x => if Row.atKey ks k x then (Row.setCells cs vs x).getD x else x),
       (atKeyRows ks k (Tbl.get db : List α)).length)
theorem execIf_put : (db.execIf (Row.put r) .all).1 =
    Tbl.set db ((Tbl.get db).map fun x => if Row.key x = Row.key r then r else x)

-- del: a delete filters the rows at the key out
theorem execIf_del (ks : List String) (k : List Sqlite.Val) :
    db.execIf (.del (Row.table α) ks k) .all =
      (Tbl.set (α := α) db ((Tbl.get db : List α).filter fun x => !Row.atKey ks k x), (atKeyRows ks k (Tbl.get db : List α)).length)

-- guarded upd (and del): only where the guard also holds; changes() > 0 exactly when some row at the key satisfied it
theorem execIf_guard (ks : List String) (k : List Sqlite.Val) (cs : List String) (vs : List Sqlite.Val) (c : Cond) :
    db.execIf (.upd (Row.table α) ks k cs vs) c =
      (Tbl.set (α := α) db ((Tbl.get db : List α).map fun x =>
          if Row.atKey ks k x && c.holds (Row.cell x) then (Row.setCells cs vs x).getD x else x),
       ((Tbl.get db : List α).filter fun x => Row.atKey ks k x && c.holds (Row.cell x)).length)
theorem guard_changes (ks : List String) (k : List Sqlite.Val) (cs : List String) (vs : List Sqlite.Val) (c : Cond) :
    0 < (db.execIf (.upd (Row.table α) ks k cs vs) c).2 ↔
      ∃ x ∈ (Tbl.get db : List α), Row.atKey ks k x = true ∧ c.holds (Row.cell x) = true
/-- On a keyed table and a full key, at most one row changes: a guarded claim has one winner. -/
theorem guard_le_one (ks : List String) (k : List Sqlite.Val) (cs : List String) (vs : List Sqlite.Val) (c : Cond)
    (hk : ks = (Row.cols α).take (Row.nkey α)) :
    (db.execIf (.upd (Row.table α) ks k cs vs) c).2 ≤ 1
```

The SQL level. `Plain st` says `st` is one of `Row.ins r`, `Row.put r`, a keyed `.del`/`.upd` of a row type's table
with cells that fit, or `logStmt`: the statements decisions emit, and the ones for which `Stmt.Pre` follows from `Good`.

```lean
def Stmt.Plain : Stmt → Prop
/-- `st` inserts an agent row named `n` (`scopeStmts` then moves that name into the scope's swarm). -/
def Stmt.insertsAgentNamed (n : String) : Stmt → Prop
def Stmt.InsertsAgent (st : Stmt) : Prop := ∃ n, st.insertsAgentNamed n
/-- `st` may make an agent row live: an agent insert, or an update that sets `ended` to NULL. -/
def Stmt.RevivesAgent : Stmt → Prop
/-- `st` may set a task's `owner`: a task insert, or a task update whose columns include `owner`. -/
def Stmt.SetsOwner : Stmt → Prop

/-- SQLite runs a decision's statement, in scope `sc`, as the model runs it on `sc`'s view. -/
theorem abs_run (hS : SqlExec S) (hd : Good d) (sc : Scope) (st : Stmt) (hp : st.Plain)
    (hev : sc.every = false ∨ ¬ st.InsertsAgent) (h : S.runs (scopeStmts sc st) d = some d') :
    Good d' ∧ abs sc d' = ((abs sc d).execIf st .all).1

-- the spec's forms, each `abs_run` composed with §3.3's model lemma
theorem abs_ins (hS : SqlExec S) (hd : Good d) (r : α) (h : S.runs (scopeStmts sc (Row.ins r)) d = some d') :
    abs sc d' = Tbl.set (abs sc d) (sortRows (Tbl.get (abs sc d) ++ [r]))
theorem abs_put (hS : SqlExec S) (hd : Good d) (r : α) (h : S.runs (scopeStmts sc (Row.put r)) d = some d') :
    abs sc d' = Tbl.set (abs sc d) ((Tbl.get (abs sc d)).map fun x => if Row.key x = Row.key r then r else x)
theorem abs_del (hS : SqlExec S) (hd : Good d) (ks k) (h : S.runs (scopeStmts sc (.del (Row.table α) ks k)) d = some d') :
    abs sc d' = Tbl.set (abs sc d) ((Tbl.get (abs sc d)).filter fun x => !Row.atKey ks k x)
theorem abs_guard (hS : SqlExec S) (hI : SqlExecIf S) (hd : Good d) (ks k cs vs c)
    (h : S.execIf (scopeStmt sc (.upd (Row.table α) ks k cs vs)) c d = some (d', n)) :
    (abs sc d', n) = (abs sc d).execIf (.upd (Row.table α) ks k cs vs) c
```

### 3.4 Reads and the frame

```lean
theorem pick_filter [Row α] (s : Sel) (rs : List α) (h : s.last = none) :
    s.pick rs = rs.filter fun x => s.cond.holds (Row.cell x)
theorem pick_last [Row α] (s : Sel) (rs : List α) (n : Nat) (h : s.last = some n) :
    s.pick rs = (rs.filter fun x => s.cond.holds (Row.cell x)).drop
      ((rs.filter fun x => s.cond.holds (Row.cell x)).length - n)
/-- A slice holds only rows of the db, in its order. -/
theorem slice_sub [Row α] [Tbl α] (db : Db) (ss next) : (Tbl.get (db.slice ss next)).Sublist (Tbl.get db)

/-- `Real.readSlice` on the model of SQLite: each table's selects with the scope's condition added, decoded. -/
def Sql.slice (S : Sql) (sc : Scope) (ss : List Sel) (next : List Table) (d : SDb) : Option Db
/-- A filtered select returns `filter p (abs d)`: the store reads the model's slice. -/
theorem slice_abs (hW : SqlSelectWhere S) (hd : Good d) (sc ss next) :
    S.slice sc ss next d = some ((abs sc d).slice ss next)
```

**The frame lemma.** An old step `f` run through `Txn.update` on its slice is `f` on the whole db. Each command family
proves it for its steps (§3.5). #79 gives the shape and the toolbox.

```lean
/-- `f` runs on its slice: on a keyed db, the step on the slice written back as a plan is the step on the db. -/
def OnSlice (ss : List Sel) (next : List Table) (f : Db → Db × α) : Prop :=
  ∀ db, Keyed db → (Txn.update ss next f).onDb db = f db

/-- What a decision answers depends only on its slice. -/
theorem slice_answer {f : Db → Db × α} (hf : OnSlice ss next f) (h : db.slice ss next = db'.slice ss next)
    (hk : Keyed db) (hk' : Keyed db') : (f db).2 = (f db').2

theorem onSlice_set (hi : { table := .task, cond := .eq "id" (.int i) } ∈ ss) (hg : ∀ u, (g u).id = u.id) :
    OnSlice ss next fun db => (db.set i g, ())
theorem onSlice_setAgent (hn : Sels.agent n ∈ ss) (hg : ∀ a, (g a).name = a.name) :
    OnSlice ss next fun db => (db.setAgent n g, ())
theorem onSlice_log (he : Table.event ∈ next) (ts ag k p dt) :
    OnSlice ss next fun db => (db.log ts ag k p dt, ())
theorem onSlice_seq {f : Db → Db × α} {g : α → Db → Db × β} (hf : OnSlice ss next f)
    (hg : ∀ a, OnSlice ss next (g a))
    (hc : ∀ db, Keyed db → ((f db).1).slice ss next = (f (db.slice ss next)).1) :
    OnSlice ss next fun db => let (d, a) := f db; g a d
```

### 3.5 The store refines the model

```lean
/-- `Real.runTxnOn` on the model of SQLite: reads by `Sql.slice`, a plan as `scopeStmts sc` of each statement, a guard
as `scopeStmt sc` with `and (c)`; none when a statement fails (the transaction rolls back). -/
def Txn.onSql (S : Sql) (sc : Scope) : Txn α → SDb → Option (SDb × α)
  | .done a, d => some (d, a)
  | .read ss n k, d => (S.slice sc ss n d).bind fun v => (k v).onSql S sc d
  | .write p k, d => (S.runs (p.flatMap (scopeStmts sc)) d).bind (k.onSql S sc)
  | .guard s c k, d => (S.execIf (scopeStmt sc s) c d).bind fun (d', n) => (k (0 < n)).onSql S sc d'

/-- Some statement `t` may write (on some answer of its reads and guards) satisfies `P`. -/
def Txn.Writes (P : Stmt → Prop) : Txn α → Prop
/-- The tables `t` may select with `inScope := false`. -/
def Txn.WideTables : Txn α → List Table
/-- Every statement `t` writes is `Plain`, whatever its reads return. -/
def Txn.Plain (t : Txn α) : Prop := ¬ t.Writes (¬ ·.Plain)
def Txn.InsertsAgent (t : Txn α) : Prop := t.Writes Stmt.InsertsAgent
def Txn.InsertsAgentNamed (n : String) (t : Txn α) : Prop := t.Writes (Stmt.insertsAgentNamed n)

/-- **The store refines the model**: what SQLite does with a transaction, seen from its scope (widened to the tables
it reads machine-wide), is `Txn.onDb` on that view, and it keeps the db `Good`. Replaces `WriteBack.write_back` and
`store_load`. -/
theorem onSql_refines (hS : SqlExec S) (hI : SqlExecIf S) (hW : SqlSelectWhere S) (sc : Scope) (t : Txn α)
    (hp : t.Plain) (hev : sc.every = false ∨ ¬ t.InsertsAgent) (hd : Good d) (h : t.onSql S sc d = some (d', a)) :
    Good d' ∧ t.onDb (absW sc t.WideTables d) = (absW sc t.WideTables d', a)

theorem update_plain (ss next) (f : Db → Db × α) : (Txn.update ss next f).Plain
```

**Per command (#80-#82): the bridge.** For each command `X` of a family, with `X.txn : Args → Txn α` the transaction
the CLI runs and `X.step : Args → Db → Db × α` its old step (kept as the decision, or as the spec when the conversion
replaced it):

```lean
theorem X.refines (args) (db : Db) (hk : Keyed db) : (X.txn args).onDb db = X.step args db
theorem X.plain (args) : (X.txn args).Plain
```

A command that is `Txn.update ss next X.step` gets `X.refines` from `OnSlice`. A guarded one (claim, `task land`, a
reap) proves it from `execIf_guard`/`guard_changes`. All decision-level theorems about `X.step` then hold of what the
binary does, through `onSql_refines`.

### 3.6 Well-formedness

```lean
/-- A view with every swarm's agents and repo `r`'s locks (finding 2). -/
def Scope.locks (r : String) : Scope := { swarm := "", repo := r, every := true }
/-- A view with every swarm's agents. -/
def Scope.all : Scope := { swarm := "", repo := "", every := true }
/-- Swarm `s`'s view. -/
def Scope.ofSwarm (s : String) : Scope := { swarm := s, repo := "" }

/-- The clauses about the machine tables and across swarms. -/
structure MachineWF (d : SDb) : Prop where
  /-- a task's owner is an agent row (of any swarm), or the user, whom `touch` gives no row -/
  owner : ∀ x ∈ (abs Scope.all d).tasks, ∀ o, x.owner = some o →
    o = Agents.HUMAN ∨ o ∈ (abs Scope.all d).agents.map (·.name)
  /-- `agent.swarm` names a swarm: a swarm's view has agents only if the swarm has a row -/
  agentSwarm : ∀ s, (abs (Scope.ofSwarm s) d).agents ≠ [] → s ∈ (abs Scope.all d).swarms.map (·.name)
  /-- `task_repo.repo` names a repo, and `task_repo.task` a task -/
  taskRepo : ∀ x ∈ (abs Scope.all d).taskRepos,
    x.repo ∈ (abs Scope.all d).repos.map (·.path) ∧ ∃ u ∈ (abs Scope.all d).tasks, u.id = x.task
  /-- `swarm_repo` names a swarm and a repo -/
  swarmRepo : ∀ x ∈ (abs Scope.all d).swarmRepos,
    x.swarm ∈ (abs Scope.all d).swarms.map (·.name) ∧ x.repo ∈ (abs Scope.all d).repos.map (·.path)
  /-- one communicator per swarm, and no agent is two swarms' communicator -/
  comms : ∀ w ∈ (abs Scope.all d).swarms, ∀ w' ∈ (abs Scope.all d).swarms, ∀ c,
    w.comms = some c → w'.comms = some c → w.name = w'.name

/-- **WF**, the machine db's invariant at time `t`. Unique keys come from `Good`; the old area invariants are about the
shared tables, so any view states them. -/
structure WF (d : SDb) (t : Int) : Prop where
  good : Good d
  /-- the board: ids unique and below the next id, owners fit states, done tasks have evidence (`Board.BInv`) -/
  board : Board.BInv (abs Scope.all d)
  /-- the queue's places are 1..n (`QueueProofs.QInv`) -/
  queue : QueueProofs.QInv (abs Scope.all d)
  /-- the message log and cursors (`Inbox.MInv`, S4's invariant) -/
  inbox : Inbox.MInv (abs Scope.all d)
  /-- one holder per lock per repo: S3 in each repo, against every swarm's agents (`Locks.Good`) -/
  locks : ∀ r, Locks.Good (abs (Scope.locks r) d) t
  machine : MachineWF d

/-- WF of the fresh schema. -/
theorem wf_fresh (t : Int) : WF freshDb t
```

Clauses #81 checks against the code before relying on them: whether a communicator stays a member of its swarm
(`join --swarm` may move it), and whether `agent.swarm` can name an ended swarm. If the code allows either, the clause
stays as written above (it does not claim them).

### 3.7 Preservation

```lean
/-- **The per-command obligation**: transaction `tx`, run in scope `sc` by SQLite on a well-formed db, commits a
well-formed one. -/
def Preserves (sc : Scope) (tx : Txn α) (t : Int) : Prop :=
  ∀ (S : Sql), SqlExec S → SqlExecIf S → SqlSelectWhere S →
    ∀ d d' a, WF d t → tx.onSql S sc d = some (d', a) → WF d' t

/-- `Preserves` in three parts, so each family proves the parts at the level they live at. The view facts are about
the shared tables, which every view holds alike (`abs_shared`), so the model step on `sc`'s view decides them. -/
def ViewPres (tx : Txn α) : Prop :=
  ∀ v, Keyed v → Board.BInv v → QueueProofs.QInv v → Inbox.MInv v →
    Board.BInv (tx.onDb v).1 ∧ QueueProofs.QInv (tx.onDb v).1 ∧ Inbox.MInv (tx.onDb v).1
/-- S3 in every repo, against every swarm's agents, kept. -/
def LockPres (sc : Scope) (tx : Txn α) (t : Int) : Prop :=
  ∀ S, SqlExec S → SqlExecIf S → SqlSelectWhere S → ∀ d d' a, Good d → (∀ r, Locks.Good (abs (Scope.locks r) d) t) →
    tx.onSql S sc d = some (d', a) → ∀ r, Locks.Good (abs (Scope.locks r) d') t
/-- The machine clauses kept. -/
def MachinePres (sc : Scope) (tx : Txn α) : Prop :=
  ∀ S, SqlExec S → SqlExecIf S → SqlSelectWhere S → ∀ d d' a, Good d → MachineWF d →
    tx.onSql S sc d = some (d', a) → MachineWF d'
theorem preserves_of (hp : tx.Plain) (hev : sc.every = false ∨ ¬ tx.InsertsAgent) (hv : ViewPres tx)
    (hl : LockPres sc tx t) (hm : MachinePres sc tx) : Preserves sc tx t
/-- A transaction that writes no lock row and makes no agent row live keeps S3 (from `isolation` and `Locks.good_sub`). -/
theorem lockPres_of_frame (hp : tx.Plain) (hn : ¬ tx.Writes fun st => st.tbl = "lock")
    (hl : ¬ tx.Writes fun st => st.RevivesAgent) : LockPres sc tx t
/-- A transaction that writes no machine table, inserts no agent and sets no task owner keeps `MachineWF`. -/
theorem machinePres_of_frame (hp : tx.Plain)
    (hn : ¬ tx.Writes fun st => st.tbl ∈ ["swarm", "repo", "swarm_repo", "task_repo"] ∨ st.InsertsAgent ∨ st.SetsOwner) :
    MachinePres sc tx

/-- A db is reachable: the fresh schema, then committed transactions, each one of `txs` in its scope. -/
inductive Reach (S : Sql) (txs : List (Scope × Σ α, Txn α)) : SDb → Prop
  | fresh : Reach S txs freshDb
  | step {d d' : SDb} (x : Scope × Σ α, Txn α) (a : x.2.1) : x ∈ txs → Reach S txs d →
      x.2.2.onSql S x.1 d = some (d', a) → Reach S txs d'

/-- **WF holds in every reachable db**, by induction over committed transactions; `begin immediate` makes the
transactions of all processes one such sequence (`Atomic` over `SDb`). -/
theorem wf_reach (hS : SqlExec S) (hI : SqlExecIf S) (hW : SqlSelectWhere S)
    (hp : ∀ x ∈ txs, Preserves x.1 x.2.2 t) (h : Reach S txs d) : WF d t
/-- One transaction as `Atomic` takes it: committed, or rolled back with nothing changed. -/
def stepSql (S : Sql) (x : Scope × Σ α, Txn α) (d : SDb) : SDb × Bool :=
  match x.2.2.onSql S x.1 d with
  | some (d', _) => (d', true)
  | none => (d, false)
theorem wf_atomic (hS : SqlExec S) (hI : SqlExecIf S) (hW : SqlSelectWhere S)
    (ran : List ((Scope × Σ α, Txn α) × Bool)) (hp : ∀ x ∈ ran, Preserves x.1.1 x.1.2.2 t)
    (h : Atomic (stepSql S) before after ran) (hb : WF before t) : WF after t
```

The family obligations are `Preserves sc (X.txn args) t` for every command `X` and every scope `sc` (with the lock
commands' clock at most `t`, as `Cross.XBefore` says today). Crash.lean's `X.*` lemmas list every transaction the CLI
runs. Each becomes one `P.*` lemma:

- **#80**: `P.Tasks.{add, claim, after, priority, renew, done, block, unblock, release, edit, drop, land, unland,
  rulesSet}`, `P.Queue.{add, rm, done, drop, hold, unhold, setQueue, tidy}`, `P.Notes.{post, takeHeld}`, `P.Db.set`.
- **#81**: `P.Msgs.{post, take, deliverStep, typedStep}`, `P.Watchd.say`, `P.Sock.failed`, `P.Locks.{lock, unlock}`,
  `P.Agents.{leave, delMeta, goAway, goBack, touch, touchWith, setRole, fenced, role, stay, endStay, setLimits, bind,
  setQueueOnly}`, `P.Hook.setStatus`, `P.Db.{log, setMeta, setAgent}`, `P.Compact.{setLimits, save}`,
  `P.Reuse.setBelow`, `P.Workspaces.upsert`, `P.Spawn.{reserve, reserveTask, unreserve}`, `P.Conflict.tickApply`,
  `P.Swarms.{create, join}` (new: the machine tables).
- **#82**: `P.Lifecycle.endStep`, `P.Watchd.{reapTask, leaseLate, landingLate1, reapLock, reapGone}`, `P.Ci.{due,
  ciPollGate, prCiGate, prWatchGate, ciPollApply, prWatchApply, prCiApply, ciCheckStep, ciNewRedTask, ciCheckFirst,
  ciCheckApply}`, the backup (a read).

`Inbox.ToIt` for finding 4, if #71 rewrites `@all` at post:

```lean
def ToIt (swarmOf : String → Option String) (n : String) (r : Msg) : Prop :=
  r.frm ≠ none ∧ r.frm ≠ some n ∧ (r.dest = some n ∨ ∃ s, swarmOf n = some s ∧ r.dest = some ("@" ++ s))
```

### 3.8 Isolation of swarms

```lean
/-- Scope `sc` sees row `r` of table `t` for writing: an agent, meta or event row of its swarm (meta scope `''` or
`sc.metaName`), the swarm row of its name, a lock or CI row of its repo, or a row of an unscoped table (task,
task_repo, msg, cursor, conflict, pairkey, workspace, which carries its own repo). -/
def Sees (sc : Scope) (t : String) (r : String → Sqlite.Val) : Prop

/-- A statement the store runs for `sc` writes only rows `sc` sees: `scopeStmts`' output, by construction. -/
def Stmt.InScope (sc : Scope) (st : Stmt) : Prop
theorem scopeStmts_inScope (sc : Scope) (st : Stmt) (hp : st.Plain) : ∀ s ∈ scopeStmts sc st, s.InScope sc

/-- **Isolation**: a transaction of a swarm scope changes only rows that scope sees, but for the one move a join
makes (the row of the name it inserts, from another swarm). -/
theorem isolation (hS : SqlExec S) (hI : SqlExecIf S) (hW : SqlSelectWhere S) (hev : sc.every = false)
    (tx : Txn α) (hp : tx.Plain) (hd : Good d) (h : tx.onSql S sc d = some (d', a)) :
    ∀ t r, ¬ Sees sc t r → ¬ (t = "agent" ∧ ∃ n, r "name" = .text n ∧ tx.InsertsAgentNamed n) →
      (r ∈ (d t).rows ↔ r ∈ (d' t).rows)

/-- The view consequence: another swarm's view changes only in the shared tables (and the repo tables when the repos
are the same). -/
theorem isolation_view (hS : SqlExec S) (hI : SqlExecIf S) (hW : SqlSelectWhere S) (hev : sc.every = false)
    (hsw : sc.swarm ≠ sc'.swarm) (tx : Txn α) (hp : tx.Plain)
    (hj : ¬ tx.InsertsAgent) (hd : Good d) (h : tx.onSql S sc d = some (d', a)) :
    (abs sc' d').agents = (abs sc' d).agents ∧ (abs sc' d').metas = (abs sc' d).metas ∧
    (abs sc' d').events = (abs sc' d).events ∧
    (sc.repo ≠ sc'.repo → (abs sc' d').locks = (abs sc' d).locks ∧ (abs sc' d').cis = (abs sc' d).cis)
```

To type the plan as the spec asks, `Db/Scope.lean` (finding 1) can return `{ p : List Stmt // ∀ s ∈ p, s.InScope sc }`
from `scopeStmts`. `runTxnOn` then runs only plans that carry the proof. That is optional: `scopeStmts_inScope` gives
the same guarantee whether or not the type carries it.

### 3.9 `RecM` (#79 defines, #82 restates its theorems)

`Rec.db : Db` becomes `Rec.db : SDb` with `Rec.scope : Scope`. `Store (RecM M)` runs `run t` as `t.onSql Sql.model
s.scope s.db`: a `none` leaves the store and throws (as Real's rolled-back IO error ends the command), and a `some`
commits (`commits := commits ++ [d']`). `view ss f` is `f` of `Sql.model.slice`. `Scoped (RecM M)` sets `s.scope` for
the inner run. `Crash.Kept`/`Keeps` take `P : SDb → Prop`. `AllOrNothing` is over `SDb`.

## 4. Old theorems → replacements

Legend:

- **V**: statement kept word for word. It is about a decision function that survives, and it holds of the binary
  through that command's `X.refines` and `onSql_refines`.
- **R**: restated in the given form.
- **X**: retired, with the reason.

The task in brackets brings it back.

### 4.1 `comparator.json` theorems

| Old | Fate |
|---|---|
| `strLit2953880` | V (ChallengeAnchor) [#82] |
| `SweepProofs.no_work_lost` | R [#82]: `Rec.db : SDb`; the run of sweeps and ends is the per-repo sweep under its repo scope; hypotheses unchanged |
| `SweepProofs.endAgent_keepsGit` | V [#82] (about git and hc calls; `endAgent`'s store writes go through `Store.run`) |
| `SweepProofs.sweep_W1` | R [#82]: `Gate.unused` over `abs (Scope.locks repo) s0.db`'s agents, every swarm's (finding 3) |
| `SweepProofs.sweepGate_W1` | R [#82]: as `sweep_W1` |
| `SweepProofs.wtRemove_only` | V [#82] |
| `SweepProofs.delRef_guarded` | V [#82] |
| `WatchdProofs.fate_keeps_stayer` | V [#82] (`Lifecycle.Reads m`, store-free) |
| `WatchdProofs.keeps_iff` | V [#82] |
| `WatchdProofs.keeps_compacting` | V [#82] |
| `WatchdProofs.lives_iff` | V [#82] |
| `WatchdProofs.lives_eq` | V [#82] |
| `WatchdProofs.reserveTask_top` | V if staffing keeps its signature; else R [#80] with `Queue.staffHead` restricted to the swarm's repos (#74's filter) as a `skip` |
| `Board.run_binv` | V [#80] (single-scope replay) + R `wf_reach`'s `board` clause (machine) |
| `Board.one_owner_all` | V [#80] + R: `∀ d, Reach S txs d → ∀ i a b, Owns (abs Scope.all d) i a → Owns (abs Scope.all d) i b → a = b` |
| `Board.done_has_evidence` | V [#80] + R from `WF.board` |
| `Board.claim_deps_done` | V [#80] |
| `Board.one_winner_all` | R [#80]: `Atomic` over `SDb` with `stepSql`, the claims of task `i` by any scopes: at most one succeeds with no release between (`guard_le_one` when claim is guarded) |
| `Board.claimed_once_all` | V [#80] + R over `Reach` |
| `Board.pool_sorted` | V [#80] |
| `Board.mem_pool` | V [#80] |
| `Board.claim_not_stopped` | V [#80] |
| `Board.claim_landing` | V [#80] |
| `Board.done_landing` | V [#80] |
| `Board.landing_waits` | V [#80] |
| `Board.land_ok` | V [#80] |
| `Board.landed_frees` | V [#80] |
| `Board.done_frees` | V [#80] |
| `Board.release_waits` | V [#80] |
| `Locks.locks_disjoint` | R [#81]: over `Reach`, `WF.locks`: per repo, against every swarm's agents |
| `Locks.no_shared_file` | R [#81]: as `locks_disjoint` |
| `Locks.atomic_good` | R [#81]: `Atomic` over `SDb` |
| `Locks.lock_ok_iff` | R [#81]: `Locks.lock` on a view with every swarm's agents (finding 2); form unchanged if #73 keeps `lock`'s signature |
| `Locks.covers_iff` | V [#81] |
| `Locks.overlaps_iff` | V [#81] |
| `Inbox.exactly_once` | R [#81]: `ToIt swarmOf` (finding 4); V if `@all` keeps its old meaning |
| `Inbox.exactly_once_atomic` | R [#81]: `Atomic` over `SDb`, `ToIt swarmOf` |
| `Inbox.shown_once` | R [#81]: as above |
| `Inbox.shown_for_it` | R [#81]: as above |
| `Inbox.cursor_passes_only_shown` | R [#81]: as above |
| `Inbox.post_unread` | R [#81]: `hd : dest = n ∨ dest = "@" ++ s ∧ swarmOf n = some s` |
| `Inbox.waiter_wakes` | V [#81] |
| `Inbox.delivery_lifts_stop` | V [#81] |
| `Inbox.release_stop` | V [#81] |
| `Inbox.nudge_frame` | V [#81] (`Db.log`; `execIf_log` ties it to the insert) |
| `QueueProofs.add_qinv` | V [#80] |
| `QueueProofs.rm_qinv` | V [#80] |
| `QueueProofs.done_qinv` | V [#80] |
| `QueueProofs.drop_qinv` | V [#80] |
| `QueueProofs.tidy_qinv` | V [#80] |
| `QueueProofs.staffing_today` | V [#80], or R with the swarm's-repos filter as for `reserveTask_top` |
| `QueueProofs.claim_not_held` | V [#80] |
| `QueueProofs.staffing_not_held` | V [#80] (or R as `staffing_today`) |
| `QueueProofs.staffHead_queue` | V [#80] (or R as `staffing_today`) |
| `QueueProofs.hold_places` | V [#80] |
| `QueueProofs.unhold_places` | V [#80] |
| `Cross.run_xinv` | R [#81]: `wf_reach` over every family's transactions in their scopes |
| `Cross.one_owner_x` | R [#81]: from `wf_reach` |
| `Cross.done_has_evidence_x` | R [#81]: from `wf_reach` |
| `Cross.locks_disjoint_x` | R [#81]: from `wf_reach` |
| `Cross.atomic_xinv` | R [#81]: `wf_atomic` |
| `Cross.claim_lapses` | R [#82]: the run is machine transactions (`Reach`); reap runs in watchd's `every` scope |
| `Cross.gone_ends` | R [#82]: as `claim_lapses` |
| `Cross.endStay_frame` | V [#81] |
| `Cross.away_keeps` | V [#81] |
| `Cross.back_keeps` | V [#81] |

### 4.2 `Proofs/*` beyond the comparator list

Each file's documented theorems, by name. The undocumented lemmas of a file (helpers: simp lemmas, unfoldings,
congruences) come back with it or go when nothing uses them. "View-level" means a statement about `Db` steps, which
stays true and gains its meaning from `X.refines`.

| File | Theorems | Fate |
|---|---|---|
| `Store.lean` | `decode_encode`, `decode_reads`, `ord_inj`, `sentinel_inj`, `setCells_other`, `setCells_map`, `setCells_self`, the `RowLaws` instances, `SDb.set_*`, `Keyed` | V [#79]: `abs` decodes with them; `RowLaws` gains instances for the four machine row types |
| `WriteBack.lean` | `write_back`, `store_load`, `load_rows`, `sortRows_eq`, `rowsPlan_keyed`, `rowsPlan_eq`, `rowsPlan_same`, `rowsPlan_unloaded`, `planOf_prefix`, `dropSame_spec`, `byKey_append`, `runs_up`, `runs_ups`, `holds_keyed`, `take_setCells`, `take_setCells_drop` | X [#79]: `loadDb`/`storeDb`/`dbPlan` are deleted (#77); replaced by `abs_run`, `slice_abs` and `onSql_refines`. `sortRows_eq` and `take_setCells*` move to `Proofs/Abs.lean` if `abs_ins` uses them. `rowsPlan` lemmas come back only if `slicePlan` needs them for `update_plain`/`OnSlice` |
| `Migrate.lean` | `migrate_step`, `migrate_version`, `migrateAll_none`, `migrateAll_last` | V [#82] while `connect` runs `migs`; plus `migs_fresh` [#79]. X if `migs`/`columns` are deleted (fresh schema, §2: no per-repo db is migrated) |
| `Tasks.lean` | `ok_of_open`, `ok_of_state`, `taken_step`, `claimed_taken`, `boardLe_total`, `boardLe_trans`, `board_sorted`, `release_other_conds`, `release_other_eq`, `release_other_enabled`, `release_other_spec`, `claim_enabled`, `done_set`, `done_keeps`, `release_ok_state`, `done_final` (and the comparator ones) | V [#80], view-level |
| `Queue.lean` | `idxOf_perm`, `setQueue_qinv`, `setQueue_frame`, `add_frame`, `done_tidy`, `places_set`, `staffHead_not_held`, `mem_staffQueue`, `staffQueue_sorted`, `red_first`, `staffing_unqueued` | V [#80]; the staffing ones R as `staffing_today` if #74 filters by the swarm's repos |
| `Msgs.lean` | `fits_prefix`, `take_window`, `atomic_inv`, `newInbox_cursor`, `posted_toIt`, `posted_urgent`, `wakes_urgent`, `wakes_none`, `wakes_spec`, `stopPending_read` | V [#81]; `posted_toIt`, `take_window` and `atomic_inv` R with `ToIt swarmOf` (finding 4) |
| `Locks.lean` | `overlaps_of_covers`, `fence_live`, `touch_self`, `grows_setAgent` | V [#81] |
| `Locks.lean` | `good_grow`, `good_sub`, `lock_good`, `unlock_good`, `leave_good`, `bind_good`, `lockHolder_some`, `lockHolder_none`, `lockHolder_agent` | R [#81]: over `abs (Scope.locks r)` (every swarm's agents); `lockHolder_*` are the edit hook's: they must hold against another swarm's locks |
| `Cross.lean` | `release_parts`, `tcmd_grows`, `tcmd_frame`, `touch_tasks`, `binv_map`, `binv_release`, `good_end`, `live_two`, `take_keep`, `lcmd_binv`, `lcmd_grows`, `end_body`, `gone_body`, `xcmd_grows` | V [#81], view-level: they give each family's `ViewPres` and `LockPres` |
| `Cross.lean` | `step_xinv`, `exactly_once_x` | R [#81]: `step_xinv` becomes the per-command `Preserves`; `exactly_once_x` over `Reach` |
| `Cross.lean` | `endStay_enabled`, `away_twice` | V [#81] |
| `Crash.lean` | the `keeps_*` combinators, `keeps_walk`/`keeps_step`/`xstep` tactics, `kept_trans`, `go_bind`, `go_eq`, `loop_ends`, `stopped_keeps` | R [#82]: `P : SDb → Prop`; `keeps_txn` becomes `keeps_run` (`Preserves sc t` → `Keeps (WF · t) (Store.run t)`), `keeps_view` |
| `Crash.lean` | `XGrow`, `xgrow_*`, `xinv_*`, `X.*` (one per transaction) | R [#80/#81/#82]: the `P.*` lemmas of §3.7, split by family |
| `Crash.lean` | `tasks_keeps`, `msgs_keeps`, `locks_keeps`, `agents_keeps`, `cost_keeps`, `ci_keeps`, `pr_keeps`, `run_keeps`, `compute_keeps`, `state_keeps`, `hook_keeps` (LEGACY since #69), `pass_keeps`, `watchd_keeps`, `groups_keep`, the `K.*` lemmas | R [#82]: `Keeps (WF · t)` per command group; `groups_keep` loses #69's `hH` hypothesis |
| `Crash.lean` | `lock_lapses`, `idle_unkept`, `unbound_unlived`, `unlaunched_ends`, `reserveAgent_row` | R [#82]: over `Reach`, reap in the `every` scope |
| `Watchd.lean` | `fateHeard_rec`, `fate_lifted`, `fateL_free`, `fate_end_free`, `fateHeard_all`, `endWhy_lifted`, `endWhy_stayer`, `keeps_eq`, `keeps_bg`, `lives_hung`, `prAct_eq`, `Sat.any`, `v_terminal_*` | V [#82] (decisions on what reads returned) |
| `Watchd.lean` | `release_free`, `endStep_free`, `endStep_refused`, `endStep_frame`, `endStep_ends`, `reapTask_spec`, `reapLock_spec`, `reapGone_spec`, `bind_changed`, `bind_ok`, `reserveAgent_max`, `unreserve_spec`, `hungStep_hung`, `orphanVictims_owned`, `guard_ok` | V [#82], view-level (with `X.refines` for each of these steps) |
| `Watchd.lean` | `replay_ran`, `atomic_ran`, `end_atomic`, `reap_atomic` | R [#82]: `Atomic` over `SDb`; the processes are any scopes' |
| `Keep.lean` | `Chain.*`, `Kept.*`, `deleteBranch_kept`, `tie_lost`, `sweep_kept`, `sweepBranches_kept` | V [#82]; R only where they read `s.db` (now `SDb`) |
| `Sweep.lean` | `git_map_ext`, `gate_intro`, `wtLines_mem`, `sc_of`, `post_of`, `post_of'`, `landedRef1_reach`, `landed_reach_spec` | V [#82]; `gate_intro` R with `Gate.unused` over every swarm's agents |
| `Trust.lean` | `need_sweep_listedOn`, `need_sweep_statusClean`, `need_sweep_cwdsProc`, `need_sweep_touchedRecent` | V [#82] (machines built from `Tools`; `GateW1` follows `Gate`) |

## 5. The work, by task

New tasks first. They are code; the proofs need them.

- **#99: machine tables and scoping through the store** (finding 1; after #74, #77; blocks #79). Done when:
  - `swarm`, `repo`, `swarm_repo`, `task_repo` are `Db` tables with row types;
  - nothing reads or writes them through `Sys.sqlAt`;
  - `task add` writes its task and `task_repo` rows in one transaction;
  - `Db/Scope.lean` holds `Scope`, `scopeCond`, `scopeStmt`, `scopeStmts`, and `Real.lean`'s reads and writes use them;
  - build and swarm-tests pass.

**#79: foundation** (after #77 and #99). It proves:

- §3.1 (`Stmt.run` AUTOINCREMENT, `runIf`, `pick`, `SqlExecIf`, `SqlSelectWhere`, `sql_consistent`, `sqlite_spec`
  cases or `sqlite_txn` extended; generalised `Atomic`/`replayOn`);
- §3.2 (`abs`, `freshDb` with its table_info case, `Good`, `Keyed`, `Tbl`, `good_fresh`, `abs_fresh`, `good_keyed`,
  `abs_shared`, `migs_fresh`);
- §3.3, both levels;
- §3.4 (`pick_*`, `slice_sub`, `Sql.slice`, `slice_abs`, `OnSlice`, `slice_answer`, the four toolbox lemmas);
- §3.5 (`Txn.onSql`, `Txn.Writes`, `Txn.WideTables`, `absW`, `Txn.Plain`, `onSql_refines`, `update_plain`);
- §3.6's `WF` and `wf_fresh`;
- §3.7's `Preserves`, `ViewPres`, `LockPres`, `MachinePres`, `preserves_of`, `lockPres_of_frame`,
  `machinePres_of_frame`, `Reach`, `stepSql`, `wf_reach`, `wf_atomic` (generic: given the `P.*`);
- §3.8 (`Sees`, `InScope`, `scopeStmts_inScope`, `isolation`, `isolation_view`);
- §3.9's `Rec` change, with `keeps_run`/`keeps_view`.

Store.lean's codec part comes back; WriteBack.lean is retired in LEGACY.md. check.sh is green: no sorry, no new axiom.

**#80: tasks and queue** (after #79). It proves:

- `X.refines`/`X.plain` for every converted task and queue command;
- `P.Tasks.*`, `P.Queue.*`, `P.Notes.*`, `P.Db.set`;
- Tasks.lean and Queue.lean back in the build: V rows as they are, R rows as §4 says (`one_winner_all` over `SDb`,
  `reserveTask_top`/staffing with the swarm's repos if #74 changed staffing);
- the machine forms of `one_owner_all`, `done_has_evidence` and `claimed_once_all` from `wf_reach`.

**#81: messages, agents, locks; isolation's uses** (after #79). It proves:

- `X.refines`/`X.plain` and `P.*` for the msgs, agents, hooks, locks, spawn, compaction and conflict transactions and
  `P.Swarms.*`;
- `ToIt swarmOf` and the exactly-once family restated;
- Locks over every swarm's agents (finding 2);
- Msgs.lean, Locks.lean and Cross.lean back in the build (Cross's `run_xinv`, `one_owner_x`, `done_has_evidence_x`,
  `locks_disjoint_x` and `atomic_xinv` from `wf_reach`/`wf_atomic`);
- a cross-swarm lock test case if #73 has none: S3 across swarms is what `WF.locks` claims.

Trust.lean moves to #82 (it is about the sweep).

**#82: watchd, sweep, keep; challenge** (after #80, #81). It proves:

- `X.refines` and `P.*` for watchd's transactions and Ci;
- Crash.lean over `SDb` (`keeps_run`, every `*_keeps`, `groups_keep` without `hH`, `stopped_keeps`);
- Watchd.lean, Keep.lean, Sweep.lean (`Gate.unused` over every swarm's agents), Trust.lean and Migrate.lean back;
- `claim_lapses`/`gone_ends` over `Reach`.

It also does the challenge work:

- `Challenge.lean`/`Solution.lean`/`comparator.json` restated per §4.1, plus the new challenged theorems
  `onSql_refines`, `wf_reach`, `isolation`, and the `X.refines` bridges for the commands whose step the challenge names
  (`TCmd.step`, `LCmd.step`, `MCmd.step`, `XCmd.step`);
- the holes gain each `X.txn` builder;
- Audit.lean's expectations;
- `challenge.sh` green, LEGACY.md emptied and deleted, check.sh green with `SWARM_PROOFS` default on again.
