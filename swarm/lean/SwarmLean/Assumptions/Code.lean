import SwarmLean.Assumptions
import SwarmLean.Lib.Ci
import SwarmLean.Lib.Watchd
import SwarmLean.Db.Plan

/-! The assumptions of `Assumptions.lean` that name the code's own functions: SQLite's statements on the store's plan
(`Db/Plan.lean`'s `Stmt`), `Machine.cwds` and `Watchd.inside`, and gh's PR list as `Ci.ghList` and `Ci.verdict` read
it. They are here so that `Assumptions.lean`, which the challenge (`Challenge.lean`) imports, imports no implementation;
none of the challenged theorems takes one of these (board #216). Each has its `(env_spec: …)` or `(sqlite_spec: …)` tag
as in `Assumptions.lean`. -/

namespace SwarmLean
open Lean (Json)

/-! ### SQLite's tables

The store's statements (Db/Plan.lean's `Stmt`, which Real.lean's `runStmts` runs) on a model of SQLite's tables.
`Stmt.run` is what SQLite's documentation says each statement does there; `Sql` is SQLite as the proofs read it, and the
assumptions say it runs each statement the store runs as `Stmt.run` says, and reads what the model holds. -/

/-- A table: its columns in order, its primary key's columns, its columns of text affinity (the others are integer),
the default of each column, and its rows, each a cell per column name. -/
structure STable where
  cols : List String
  keys : List String
  text : List String
  dflt : String → Sqlite.Val
  rows : List (String → Sqlite.Val)

/-- A db: each table by name. -/
abbrev SDb := String → STable

/-- `db` with table `t` replaced by `T`. -/
def SDb.set (db : SDb) (t : String) (T : STable) : SDb := fun u => if u = t then T else db u

/-- Row `r` holds `k` in columns `ks`: SQLite's `ks₁=? and …` with `k` bound, for int and text cells. -/
def keyAt (r : String → Sqlite.Val) (ks : List String) (k : List Sqlite.Val) : Bool :=
  (ks.map r).flatMap Sqlite.Val.ord == k.flatMap Sqlite.Val.ord

/-- `r` with columns `cs` set to `vs`. -/
def setCells (r : String → Sqlite.Val) (cs : List String) (vs : List Sqlite.Val) : String → Sqlite.Val :=
  fun c => ((cs.zip vs).lookup c).getD (r c)

/-- The default a column declaration gives (`int default 2`: 2), NULL when it gives none. -/
def declDefault (d : String) : Sqlite.Val :=
  match d.splitOn " default " with
  | [_, v] => match v.toInt? with | some i => .int i | none => .text v
  | _ => .null

/-- A value as a text column stores it: a number as its text. -/
def textAff : Sqlite.Val → Sqlite.Val
  | .int i => .text (toString i)
  | v => v

/-- What SQLite does with a statement on `db`; none when it fails: an insert whose key a row has, an add of a column
the table has or to a table that has none, a drop of a column it lacks. -/
def Stmt.run (db : SDb) : Stmt → Option SDb
  | .del t ks k =>
    let T := db t
    some (db.set t { T with rows := T.rows.filter (fun r => !keyAt r ks (k.map Sqlite.Val.bound)) })
  | .upd t ks k cs vs =>
    let T := db t
    let f := fun r => if keyAt r ks (k.map Sqlite.Val.bound) then setCells r cs (vs.map Sqlite.Val.bound) else r
    some (db.set t { T with rows := T.rows.map f })
  | .ins t cs vs =>
    let T := db t
    let r := setCells T.dflt cs (vs.map Sqlite.Val.bound)
    if T.rows.any (fun x => keyAt x T.keys (T.keys.map r)) then none
    else some (db.set t { T with rows := T.rows ++ [r] })
  | .addCol t d =>
    let T := db t
    let c := colName d
    let v := declDefault d
    let tx := if (d.splitOn " ")[1]? == some "text" then T.text ++ [c] else T.text
    let rs := T.rows.map (fun r => setCells r [c] [v])
    if T.cols.isEmpty || T.cols.contains c then none
    else some (db.set t { T with cols := T.cols ++ [c], text := tx, dflt := setCells T.dflt [c] [v], rows := rs })
  | .dropAfter =>
    let T := db "task"
    let copy := fun (r : String → Sqlite.Val) => if T.text.contains "deps" then textAff (r "after") else r "after"
    let f := fun r => if (r "deps").cls == 0 && (r "after").cls != 0 then setCells r ["deps"] [copy r] else r
    if T.cols.contains "after" then some (db.set "task" { T with cols := T.cols.erase "after", rows := T.rows.map f })
    else none

/-- The cells `vs` fit columns `cs` of `T`: each NULL, an int in an integer column or a text in a text one, so SQLite
stores it as it is. -/
def Fits (T : STable) (cs : List String) (vs : List Sqlite.Val) : Prop :=
  cs.length = vs.length ∧ (∀ c ∈ cs, c ∈ T.cols) ∧
    ∀ p ∈ cs.zip vs, p.2.cls = 0 ∨ (p.2.cls = 1 ∧ p.1 ∉ T.text) ∨ (p.2.cls = 3 ∧ p.1 ∈ T.text)

/-- Key `k` in columns `ks` compares with each row of `T` within one class: both ints or both texts, column by
column. -/
def KeyClass (T : STable) (ks : List String) (k : List Sqlite.Val) : Prop :=
  (∀ c ∈ ks, c ∈ T.cols) ∧ (∀ v ∈ k, v.cls = 1 ∨ v.cls = 3) ∧ ∀ r ∈ T.rows, (ks.map r).map Sqlite.Val.cls = k.map Sqlite.Val.cls

/-- Where the model is SQLite: keys compared within a class, cells that fit their columns, the migrations of
`columns`, an after holding no float. -/
def Stmt.Pre (db : SDb) : Stmt → Prop
  | .del t ks k => KeyClass (db t) ks k
  | .upd t ks k cs vs => KeyClass (db t) ks k ∧ Fits (db t) cs vs
  | .ins t cs vs => Fits (db t) cs vs ∧ KeyClass (db t) (db t).keys ((db t).keys.map (setCells (db t).dflt cs vs))
  | .addCol t d => (t, d) ∈ columns
  | .dropAfter => ∀ r ∈ (db "task").rows, (r "after").cls ≠ 2

/-- SQLite as the store proofs read it. -/
structure Sql where
  /-- the db after `Conn.exec` runs `st.sql` on `db`; none when it fails -/
  exec : Stmt → SDb → Option SDb
  /-- the rows `select cs from t` returns on `db` -/
  select : SDb → String → List String → List (Array Sqlite.Val)
  /-- the column names `pragma table_info(t)` returns on `db` -/
  tableInfo : SDb → String → List String

/-- SQLite: each statement the store runs does what its documentation says (`Stmt.run`): a delete or update by key
takes the rows whose key cells equal the bound key, an insert adds the row with the bound cells and each other column's
default and fails on a key a row has, `alter table add column` gives each row the column's default, and the after
migration copies after into a NULL deps (as text, deps being a text column) and drops it (sqlite_spec: sqlite_dml,
sqlite_alter). -/
def SqlExec (S : Sql) : Prop := ∀ db st, st.Pre db → S.exec st db = st.run db

/-- SQLite: `select cs from t` returns each row's cells in `cs`, in some order (sqlite_spec: sqlite_dml). -/
def SqlSelect (S : Sql) : Prop :=
  ∀ db t cs, (∀ c ∈ cs, c ∈ (db t).cols) → (S.select db t cs).Perm ((db t).rows.map fun r => (cs.map r).toArray)

/-- SQLite: `pragma table_info(t)` lists t's columns (sqlite_spec: sqlite_alter). -/
def SqlTableInfo (S : Sql) : Prop := ∀ db t, S.tableInfo db t = (db t).cols

/-- The model itself as SQLite. -/
def Sql.model : Sql where
  exec st db := st.run db
  select db t cs := (db t).rows.map fun r => (cs.map r).toArray
  tableInfo db t := (db t).cols

/-- The SQLite assumptions hold together: the model has them. -/
theorem sql_consistent : SqlExec .model ∧ SqlSelect .model ∧ SqlTableInfo .model :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => List.Perm.refl _, fun _ _ => rfl⟩

variable (M : Tools)

-- BEGIN CHALLENGE COPY Assumptions/Code.lean
/-- processes: `Machine.cwds`, when it answers, lists for every process inside a worktree a working directory whose
realpath (on the machine it left) is inside it (Linux: each /proc/<pid>/cwd; macOS: lsof) (env_spec: cwds_proc). -/
abbrev CwdsProc : Prop := ∀ (s : Rec M) cs wt, (Rec.go Machine.cwds s).1 = .ok (some cs) → M.Inside s.w wt →
  ∃ c ∈ cs, Watchd.inside ((M.realpath (Rec.go Machine.cwds s).2.w c.2).getD c.2) wt = true
-- END CHALLENGE COPY Assumptions/Code.lean

/-! ### gh -/

/-- The PR list `gh pr list --state all --limit 50 --json …` prints (ci.pr_watch's poll), as `Ci.ghList` reads it. -/
def prList (o : ProcOut) : Option (List Json) := Ci.ghList (some o) ""

/-- gh: the verdict `Ci.verdict` reads off a listed PR's `statusCheckRollup` is the state of its head's checks
(env_spec: gh_checks). -/
def GhChecks : Prop := ∀ w repo fields o prs x p,
  M.out w ["gh", "pr", "list", "--state", "all", "--limit", "50", "--json", fields] repo = some o → prList o = some prs →
  x ∈ prs → (x.getObjValAs? Int "number").toOption = some p →
  Ci.verdict (x.getObjVal? "statusCheckRollup").toOption = M.checks w p

/-- gh: a listed PR that is not closed has state MERGED when it is merged, else OPEN (env_spec: gh_state). -/
def GhState : Prop := ∀ w repo fields o prs x p,
  M.out w ["gh", "pr", "list", "--state", "all", "--limit", "50", "--json", fields] repo = some o → prList o = some prs →
  x ∈ prs → (x.getObjValAs? Int "number").toOption = some p → Json.fstr x "state" ≠ some "CLOSED" →
  Json.fstr x "state" = some (if M.merged w p then "MERGED" else "OPEN")

/-- The tool assumptions hold together: the idle machine has them all. That the real tools have them is what
swarm-tests' env_spec cases test. -/
theorem consistent : AncestorReach .idle ∧ SameContentReach .idle ∧ StatusClean .idle ∧ ListedOn .idle ∧
    WtRemove .idle ∧ DelRef .idle ∧ BranchD .idle ∧ RevParseHead .idle ∧ GitReadsKeep .idle ∧ ToolsKeep .idle ∧ HcLsLive .idle ∧ HcKillEnds .idle ∧ HcRmKeeps .idle ∧ HcSendTargets .idle ∧
    HcRunStarts .idle ∧ CgroupKillKeeps .idle ∧ UdsSendKeeps .idle ∧ Kill0Alive .idle ∧ CwdsProc .idle ∧ TouchedRecent .idle ∧
    NowMono .idle ∧ GhChecks .idle ∧ GhState .idle := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [AncestorReach, SameContentReach, StatusClean, ListedOn, WtRemove, DelRef, BranchD, RevParseHead, GitReadsKeep,
      ToolsKeep, HcLsLive, HcKillEnds, HcRmKeeps,
      HcSendTargets, HcRunStarts, CgroupKillKeeps, UdsSendKeeps, Kill0Alive, CwdsProc, TouchedRecent, NowMono, GhChecks, GhState,
      Tools.idle, Tools.SameRepo, Ok0]

end SwarmLean
