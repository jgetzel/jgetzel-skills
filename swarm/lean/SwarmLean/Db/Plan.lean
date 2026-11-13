import SwarmLean.Db
import Std.Data.HashMap

/-! The store's statements as data (board #134): what `storeDb` writes back and what `connect` migrates, each a list of
`Stmt` that Real.lean's `runStmts` runs, and how `loadRows` decodes what a select returned. Pure, so the proofs
(Proofs/Store.lean) are about the plans the code runs. -/

namespace SwarmLean
open Sqlite (Val)

/-- A cell as integers: ordered as SQLite orders key cells (NULL, then numbers, then text by code point; a float by its
bits, which no key holds), and equal for two int or text cells exactly when they are. Rows are keyed and sorted by it. -/
def Sqlite.Val.ord : Val → List Int
  | .null => [0]
  | .int i => [1, i]
  | .real f => [2, f.toBits.toNat]
  | .text s => 3 :: s.toList.map (fun c => (c.toNat : Int)) ++ [-1]

/-- A row's primary key, as `Val.ord`s of its key cells. -/
def Row.key [Row α] (r : α) : List Int := ((Row.enc r).take (Row.nkey α)).flatMap Val.ord

/-- Whether keyed rows are in key order. -/
def keysSorted : List (List Int × α) → Bool
  | a :: b :: l => decide (a.1 ≤ b.1) && keysSorted (b :: l)
  | _ => true

/-- Rows in key order: SQLite returns a select's rows in no order the store relies on (`loadRows` asks for key order,
so this is mostly a check). Each key is computed once, not per comparison (board #138). -/
def sortRows [Row α] (rs : List α) : List α :=
  let ps := rs.map fun r => (Row.key r, r)
  if keysSorted ps then rs else (ps.mergeSort fun a b => decide (a.1 ≤ b.1)).map (·.2)

/-- The rows a select of `Row.cols α` from `Row.table α` returned, decoded, in key order. -/
def decodeRows [Row α] (rows : List (Array Val)) : Except String (List α) :=
  sortRows <$> rows.mapM fun v => (Row.dec v : Except String α).mapError fun e => s!"{Row.table α}: {e}"

/-- A statement the store runs. -/
inductive Stmt
  /-- delete from `t` the rows whose key columns `ks` hold `k` -/
  | del (t : String) (ks : List String) (k : List Val)
  /-- set columns `cs` to `vs` in the rows of `t` whose key columns `ks` hold `k` -/
  | upd (t : String) (ks : List String) (k : List Val) (cs : List String) (vs : List Val)
  /-- insert into `t` a row holding `vs` in columns `cs` -/
  | ins (t : String) (cs : List String) (vs : List Val)
  /-- add column `decl` (a name, a type, maybe a default) to `t` -/
  | addCol (t decl : String)
  /-- copy task.after into deps where deps is NULL, then drop column after -/
  | dropAfter

/-- `k1=? and k2=? …` -/
def whereKey (ks : List String) : String := " and ".intercalate (ks.map (· ++ "=?"))

/-- The SQL a statement runs, each with its parameters. -/
def Stmt.sql : Stmt → List (String × List Val)
  | .del t ks k => [(s!"delete from {t} where {whereKey ks}", k)]
  | .upd t ks k cs vs => [(s!"update {t} set {", ".intercalate (cs.map (· ++ "=?"))} where {whereKey ks}", vs ++ k)]
  | .ins t cs vs => [(s!"insert into {t}({", ".intercalate cs}) values({", ".intercalate (cs.map fun _ => "?")})", vs)]
  | .addCol t d => [(s!"alter table {t} add column {d}", [])]
  | .dropAfter => [("update task set deps=after where deps is null and after is not null", []),
      ("alter table task drop column after", [])]

/-- The rows of `l` by key. -/
def byKey [Row α] (l : List α) : Std.HashMap (List Int) α := Std.HashMap.ofList (l.map fun r => (Row.key r, r))

/-- The statement the write-back runs for new row `r`, given the old rows by key: none when it is unchanged, an update
of the columns but the key when it changed, an insert when it is new. -/
def upOf [Row α] [BEq α] (oldM : Std.HashMap (List Int) α) (r : α) : Option Stmt :=
  let n := Row.nkey α
  match oldM[Row.key r]? with
  | some o => if o == r then none else
    some (.upd (Row.table α) ((Row.cols α).take n) ((Row.enc r).take n) ((Row.cols α).drop n) ((Row.enc r).drop n))
  | none => some (.ins (Row.table α) (Row.cols α) (Row.enc r))

/-- The statement the write-back runs for old row `r`, given the new rows by key: a delete when it is gone. -/
def delOf [Row α] (newM : Std.HashMap (List Int) α) (r : α) : Option Stmt :=
  if newM.contains (Row.key r) then none else
    some (.del (Row.table α) ((Row.cols α).take (Row.nkey α)) ((Row.enc r).take (Row.nkey α)))

/-- The write-back of `new` over `old` by primary key: a delete for each row gone, then `upOf` each new row. Each map
is built once, as an argument: built inside a lambda, it was rebuilt per row (82 s a transaction on 12k events, board
#138). -/
def planOf [Row α] [BEq α] (old new : List α) : List Stmt :=
  old.filterMap (delOf (byKey new)) ++ new.filterMap (upOf (byKey old))

/-- `old` and `new` past their longest common prefix. -/
def dropSame [BEq α] : List α → List α → List α × List α
  | a :: as, b :: bs => if a == b then dropSame as bs else (a :: as, b :: bs)
  | as, bs => (as, bs)

/-- The write-back of `new` over `old` (the rows loaded, or none if the table was not): `planOf` past their common
prefix, which most steps leave as loaded (an event appended changes only the end), so a step costs the rows it changed
plus one comparison per row kept (board #138). Columns Lean does not know keep their values. -/
def rowsPlan [Row α] [BEq α] (old new : List α) : List Stmt :=
  let p := dropSame old new
  planOf p.1 p.2

/-- The write-back of every table of `new` over what `old` loaded. -/
def dbPlan (old new : Db) : List Stmt :=
  rowsPlan old.agents new.agents ++ rowsPlan old.msgs new.msgs ++ rowsPlan old.cursors new.cursors ++
  rowsPlan old.tasks new.tasks ++ rowsPlan old.locks new.locks ++ rowsPlan old.conflicts new.conflicts ++
  rowsPlan old.pairkeys new.pairkeys ++ rowsPlan old.metas new.metas ++ rowsPlan old.events new.events ++
  rowsPlan old.workspaces new.workspaces ++ rowsPlan old.cis new.cis

/-- db.lua's COLUMNS: the columns added to dbs made before them. -/
def columns : List (String × String) :=
  [("agent", "wt text"), ("lock", "seen int default 0"), ("task", "model text"), ("task", "question text"),
  ("agent", "claude_pid int"), ("task", "created_at int"), ("task", "first_claimed_at int"), ("task", "done_at int"),
  ("task", "dropped_at int"), ("task", "pr int"), ("task", "merged_at int"), ("task", "ci_conclusion text"),
  ("task", "ci_green_at int"), ("task", "claim_ctx int"), ("task", "done_ctx int"), ("task", "deps text"),
  ("ci", "workflow text"), ("task", "answer text"), ("task", "effort text"),
  ("agent", "role text"), ("agent", "stay text"), ("task", "base text"), ("task", "stop_to text"),
  ("task", "stop_msg int"), ("task", "priority int default 2"),
  ("task", "qpos int"), ("task", "hold text")]

/-- A column declaration's name. -/
def colName (decl : String) : String := String.ofList (decl.toList.takeWhile (· ≠ ' '))

/-- The migrations of an older db, in order (schema version n has the first n): each column of `columns` added, then
task.after moved into deps. -/
def migs : List Stmt := columns.map (fun (t, d) => .addCol t d) ++ [.dropAfter]

/-- Whether a db whose table `t` has the columns `has t` needs migration `m`: a column it lacks, an after it has. -/
def Stmt.needed (has : String → List String) : Stmt → Bool
  | .addCol t d => !(has t).contains (colName d)
  | .dropAfter => (has "task").contains "after"
  | _ => false

/-- The tables the migrations touch. -/
def migTables : List String := ["agent", "lock", "task", "ci"]

end SwarmLean
