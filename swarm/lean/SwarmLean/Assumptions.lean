import SwarmLean.Store
import SwarmLean.Lib.Ci
import SwarmLean.Lib.Watchd
import SwarmLean.Db.Plan

/-! Every assumption the proofs of swarm-lean make about the world outside the code, in one file (board #109).

The code reaches the world only through the classes of World.lean and Sys.lean; the proofs are about the functions it
runs, and nothing here is an axiom. Each assumption is a definition, a `Prop`, that a theorem takes as a hypothesis, so
a theorem reads "these assumptions about the world → this guarantee", and `Audit.lean` counts the theorems that take
each. They are swarm/model's `Env.lean` hypotheses moved onto the code's own calls, deduplicated with what #103-#106
used:

- the store: `Atomic`, the one assumption #103-#106 took, which also stands for Env.lean's five sqlite hypotheses
  (`SqliteBegin`, `SqliteRead`, `SqliteWrite`, `SqliteCommit`, `SqliteRollback`): the code runs every write as one
  `BEGIN IMMEDIATE … COMMIT` (`Store.txn`), and what those five give such a transaction is that concurrent ones apply
  in some order;
- the tools, through `Tools`: what a command line answers (`Proc.output`, `Git.git`), what `Sys.pidAlive`,
  `Sys.mtime`, `Clock.now` and `Machine.cwds` return, and what is true of the repo, the terminals, the processes and
  the PRs. Each assumption below says that one answer means one truth, as Env.lean's did of its `Tools`.

Each assumption names, in its `(env_spec: …)` or `(sqlite_spec: …)` tag, the case of swarm-tests (Tests/Spec/Env.lean,
Tests/Spec/Sqlite.lean) that tests it against the real tool (check.sh fails on a tag with no case there).
`consistent`: one machine has them all. -/

namespace SwarmLean
open Lean (Json)

/-- What "the store is well behaved" means, assumed of the real store and not proved: when processes ran their
requests `ran` (each with the answer it got) at once on a store holding `before` and left `after`, the requests
applied one after another in some order give those answers and `after` (sqlite_spec: sqlite_begin, sqlite_write,
sqlite_commit, sqlite_rollback). -/
def Atomic (step : τ → Db → Db × α) (before after : Db) (ran : List (τ × α)) : Prop :=
  ∃ order : List (τ × α), order.Perm ran ∧ replay step before (order.map (·.1)) = (after, order)

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

/-- A call of the code that changes the machine other than a command line: a line written to stdout or stderr, a file
written, a directory made, a hard link, a file removed, an environment variable set, a sleep, statements run on an
SQLite file. -/
inductive Eff
  | line (err : Bool) (s : String)
  | write (path text : String)
  | mkdirp (path : String)
  | link (a b : String)
  | remove (path : String)
  | setenv (k v : String)
  | sleep (ms : Nat)
  | sql (path schema : String) (stmts : List (String × List Sqlite.Val)) (ro : Bool)

/-- The machine at one moment, as the assumptions read it: what each of the code's calls to the world (each method of
World.lean's and Sys.lean's classes but `Store`) answers there, the world after a command or an effect, and what is true
of the repo, hc's terminals, the processes and GitHub's PRs. Any value of this type
is a machine: each call may answer anything (a failed call is one of the answers). -/
structure Tools where
  /-- the machine at one moment -/
  World : Type
  /-- what `Proc.output argv cwd []` returns in `w`: exit code and output, none when the program could not run -/
  out : World → List String → Option String → Option ProcOut
  /-- what `Git.git args cwd` returns in `w`: git's stdout when it exits 0 -/
  git : World → List String → Option String → Option String
  /-- the machine after `argv` ran from `cwd` in `w` -/
  after : World → List String → Option String → World
  /-- what `Sys.pidAlive p` (kill(p, 0) == 0) returns in `w` -/
  pidAlive : World → Int → Bool
  /-- what `Sys.mtime path` returns in `w` -/
  mtime : World → String → Option Int
  /-- what `Clock.now` returns in `w` -/
  now : World → Int
  /-- what `Clock.hhmm t` returns in `w` -/
  hhmm : World → Int → String
  /-- what `Env.var k` returns in `w` -/
  var : World → String → Option String
  /-- what `Env.cwd` returns in `w` -/
  cwd : World → String
  /-- what `Env.stdin` returns in `w` -/
  stdin : World → String
  /-- what `Fs.read path` returns in `w` -/
  read : World → String → Option String
  /-- what `Fs.list dir` returns in `w` -/
  list : World → String → Option (List String)
  /-- what `Sys.getpid` returns in `w` -/
  getpid : World → Int
  /-- what `Sys.getppid` returns in `w` -/
  getppid : World → Int
  /-- what `Sys.nowF` returns in `w` -/
  nowF : World → Float
  /-- what `Sys.date fmt t` returns in `w` -/
  date : World → String → Int → String
  /-- what `Sys.hostname` returns in `w` -/
  hostname : World → String
  /-- what `Sys.environ` returns in `w` -/
  environ : World → List (String × String)
  /-- what `Sys.realpath path` returns in `w` -/
  realpath : World → String → Option String
  /-- what `Sys.readlink path` returns in `w` -/
  readlink : World → String → Option String
  /-- what `Sys.kind path follow` returns in `w` -/
  kind : World → String → Bool → Kind
  /-- what `Proc.launcherDir` returns in `w` -/
  launcherDir : World → Option String
  /-- what `Proc.exec argv` returns in `w` (it returns only when the exec failed) -/
  exec : World → List String → String
  /-- what `Sys.exec argv opts` returns in `w` -/
  run : World → List String → RunOpts → ProcOut
  /-- the machine after effect `e` in `w` -/
  effect : World → Eff → World
  /-- what effect `e` returns in `w` (`Fs.write`, `Sys.mkdirp`, `Sys.link`, `Sys.remove`: whether it worked) -/
  ok : World → Eff → Bool
  /-- the rows `Sys.sqlAt` returns in `w` -/
  rows : World → Eff → List (Array (Array Sqlite.Val))
  /-- `w'` comes after `w`, whatever the swarm and the world did in between -/
  Later : World → World → Prop
  /-- the repo, checked out at `cwd`, holds every change of commit `ref` in `b` (by ancestry or the same content) -/
  Holds : World → String → String → String → Prop
  /-- worktree `wt` is there -/
  There : World → String → Prop
  /-- worktree `wt` has something uncommitted, an untracked file included -/
  Dirty : World → String → Prop
  /-- branch `b`'s tip -/
  tip : World → String → Option String
  /-- some process's working directory is inside worktree `wt` -/
  Inside : World → String → Prop
  /-- worktree `wt` was used (an edit, a commit, a checkout) in the last `Watchd.SWEEP_IDLE` seconds -/
  Recent : World → String → Prop
  /-- hc's terminal `h` is live -/
  Live : World → String → Prop
  /-- process `p` is in the process table (running, or a zombie its parent has not reaped) -/
  Running : World → Int → Prop
  /-- the lines typed into terminal `h` so far, in order -/
  typed : World → String → List String
  /-- PR `p`'s head checks as GitHub runs them: "pending" until every check finished, then "green" or "red" -/
  checks : World → Int → String
  /-- PR `p` is merged into its base -/
  merged : World → Int → Bool

variable (M : Tools)

/-- The repo is the same in `w` and `w'`: every worktree there or not and dirty or not as it was, every branch tip,
and what each commit's changes are in. -/
def Tools.SameRepo (w w' : M.World) : Prop :=
  (∀ b, M.tip w' b = M.tip w b) ∧ (∀ x, (M.There w' x ↔ M.There w x) ∧ (M.Dirty w' x ↔ M.Dirty w x)) ∧
    ∀ cwd a b, M.Holds w' cwd a b ↔ M.Holds w cwd a b

/-- The command exited 0. -/
def Ok0 (o : Option ProcOut) : Prop := ∃ x, o = some x ∧ x.code = 0

/-! ### The code on a machine

`RecM M` runs the code on machine `M` and records what it did: every command line (`Proc.output`, `Sys.exec`,
`Proc.exec`), git command (`Git.git`) and effect (`Eff`), each with the machine it ran on. A command or an effect moves
the machine on (`after`, `effect`); a read answers from the machine as it is; `Git.git` is a read (Tools gives no
machine after it: the code runs git's writes through `Proc.output`), recorded all the same. The store is a `Db` the
transactions apply to in turn. A theorem about the code on a machine runs it in `RecM M` from any state. -/

/-- A call that can change the machine: a command line run from `cwd`, a git command, an effect. -/
inductive Call
  | cmd (argv : List String) (cwd : Option String)
  | git (args : List String) (cwd : Option String)
  | eff (e : Eff)

/-- The recording world's state: the machine now, the store, and every call so far with the machine it ran on. -/
structure Rec where
  w : M.World
  db : Db
  log : List (M.World × Call)

/-- The code run on machine `M`, recording its calls; an early exit keeps the state. -/
abbrev RecM := ExceptT Exit (StateM (Rec M))

/-- `argv` run with `env` set (`some`) and unset (`none`): `env -u K … K=V … argv`, the same command. -/
def withEnv (env : List (String × Option String)) (argv : List String) : List String :=
  if env.isEmpty then argv else
    "env" :: (env.filterMap fun (k, v) => if v.isNone then some k else none).flatMap (["-u", ·]) ++
      (env.filterMap fun (k, v) => v.map (k ++ "=" ++ ·)) ++ argv

namespace Rec
variable {M}

/-- Runs command `argv` from `cwd`, answering `ans` of the machine it ran on: recorded, and the machine moves on. -/
def cmd (argv : List String) (cwd : Option String) (ans : M.World → α) : RecM M α :=
  modifyGet fun s => (ans s.w, { s with w := M.after s.w argv cwd, log := s.log ++ [(s.w, .cmd argv cwd)] })

/-- Effect `e`, answering `ans` of the machine it ran on: recorded, and the machine moves on. -/
def eff (e : Eff) (ans : M.World → α) : RecM M α :=
  modifyGet fun s => (ans s.w, { s with w := M.effect s.w e, log := s.log ++ [(s.w, .eff e)] })

/-- A read of the machine as it is. -/
def ask (f : M.World → α) : RecM M α := modifyGet fun s => (f s.w, s)

end Rec

instance : Store (RecM M) where
  txn _ f := modifyGet fun s => let (db, a) := f s.db; (a, { s with db })
instance : Clock (RecM M) where
  now := Rec.ask M.now
  hhmm t := Rec.ask (M.hhmm · t)
instance : Env (RecM M) where
  var k := Rec.ask (M.var · k)
  out l := Rec.eff (.line false l) fun _ => ()
  err l := Rec.eff (.line true l) fun _ => ()
  stdin := Rec.ask M.stdin
  cwd := Rec.ask M.cwd
instance : Fs (RecM M) where
  read p := Rec.ask (M.read · p)
  list p := Rec.ask (M.list · p)
  write p t := Rec.eff (.write p t) (M.ok · (.write p t))
instance : Proc (RecM M) where
  output argv cwd env := Rec.cmd (withEnv (env.map fun (k, v) => (k, some v)) argv) cwd
    (M.out · (withEnv (env.map fun (k, v) => (k, some v)) argv) cwd)
  exec argv := Rec.cmd argv none (M.exec · argv)
  launcherDir := Rec.ask M.launcherDir
instance : Git (RecM M) where
  git args cwd := modifyGet fun s => (M.git s.w args cwd, { s with log := s.log ++ [(s.w, .git args cwd)] })
instance : Sys (RecM M) where
  getpid := Rec.ask M.getpid
  getppid := Rec.ask M.getppid
  pidAlive p := Rec.ask (M.pidAlive · p)
  sleep ms := Rec.eff (.sleep ms) fun _ => ()
  nowF := Rec.ask M.nowF
  date f t := Rec.ask (M.date · f t)
  hostname := Rec.ask M.hostname
  environ := Rec.ask M.environ
  setenv k v := Rec.eff (.setenv k v) fun _ => ()
  realpath p := Rec.ask (M.realpath · p)
  readlink p := Rec.ask (M.readlink · p)
  kind p f := Rec.ask (M.kind · p f)
  mtime p := Rec.ask (M.mtime · p)
  mkdirp p := Rec.eff (.mkdirp p) (M.ok · (.mkdirp p))
  link a b := Rec.eff (.link a b) (M.ok · (.link a b))
  remove p := Rec.eff (.remove p) (M.ok · (.remove p))
  exec argv o := Rec.cmd (withEnv o.env argv) o.cwd (M.run · argv o)
  sqlAt p sc st ro := Rec.eff (.sql p sc st ro) (M.rows · (.sql p sc st ro))

/-- `x` run on the machine from state `s`: its result and the state it left. -/
@[irreducible] def Rec.go {M : Tools} (x : RecM M α) (s : Rec M) : Except Exit α × Rec M := x.run.run s

/-! ### git -/

/-- git: `git -C cwd merge-base --is-ancestor ref b` exiting 0 means `b` holds `ref`'s changes (env_spec: ancestor_reach). -/
def AncestorReach : Prop := ∀ w cwd ref b,
  Ok0 (M.out w ["git", "-C", cwd, "merge-base", "--is-ancestor", ref, b] none) → M.Holds w cwd ref b

/-- git: when `git -C cwd merge-base b ref` prints the merge base `mb`, then `git diff --name-only -z mb ref` lists some
files and `git diff --quiet ref b -- <them>` exits 0, each on the machine the one before left, `b` holds `ref`'s changes
there: a squash or rebase merge (Lifecycle.landedRef1's second check) (env_spec: same_content_reach). -/
def SameContentReach : Prop := ∀ w cwd ref b o d,
  let a1 := ["git", "-C", cwd, "merge-base", b, ref]
  let w1 := M.after w a1 none
  let a2 := ["git", "-C", cwd, "diff", "--name-only", "-z", strip o.stdout, ref]
  let w2 := M.after w1 a2 none
  let files := (d.stdout.splitOn "\x00").filter (· ≠ "")
  M.out w a1 none = some o → o.code = 0 → strip o.stdout ≠ "" → M.out w1 a2 none = some d → d.code = 0 → files ≠ [] →
  Ok0 (M.out w2 (["git", "-C", cwd, "diff", "--quiet", ref, b, "--"] ++ files) none) → M.Holds w2 cwd ref b

/-- git: a worktree that is there and whose `git --no-optional-locks -C wt status --porcelain` prints nothing but space
has nothing uncommitted, untracked files included (env_spec: status_clean). -/
def StatusClean : Prop := ∀ w wt o, M.There w wt →
  M.out w ["git", "--no-optional-locks", "-C", wt, "status", "--porcelain"] none = some o → o.code = 0 → strip o.stdout = "" →
    ¬ M.Dirty w wt

/-- git: the path on a `worktree <path>` line `git worktree list --porcelain` prints is a worktree that is there
(env_spec: listed_on). -/
def ListedOn : Prop := ∀ w cwd o l,
  M.out w ["git", "worktree", "list", "--porcelain"] cwd = some o → o.code = 0 → l ∈ splitlines o.stdout →
  l.startsWith "worktree " = true → M.There w (l.drop 9).toString

/-- git: `git -C main worktree remove wt` takes a clean worktree away and nothing else (every branch, every other
worktree, every commit stay), and refuses a dirty one, changing nothing (env_spec: wt_remove). -/
def WtRemove : Prop := ∀ w main wt,
  let w' := M.after w ["git", "-C", main, "worktree", "remove", wt] none
  (M.There w wt ∧ ¬ M.Dirty w wt → ¬ M.There w' wt) ∧ (M.Dirty w wt → M.SameRepo w w') ∧
    (∀ b, M.tip w' b = M.tip w b) ∧ (∀ x, x ≠ wt → (M.There w' x ↔ M.There w x) ∧ (M.Dirty w' x ↔ M.Dirty w x)) ∧
    ∀ cwd a b, M.Holds w' cwd a b ↔ M.Holds w cwd a b

/-- git: `git -C main update-ref -d refs/heads/b k` deletes branch `b` if its tip is `k`, and else changes nothing; no
other branch, no worktree and no commit changes (env_spec: del_ref). -/
def DelRef : Prop := ∀ w main b k,
  let w' := M.after w ["git", "-C", main, "update-ref", "-d", "refs/heads/" ++ b, k] none
  M.tip w' b = (if M.tip w b = some k then none else M.tip w b) ∧ (∀ b', b' ≠ b → M.tip w' b' = M.tip w b') ∧
    (∀ x, (M.There w' x ↔ M.There w x) ∧ (M.Dirty w' x ↔ M.Dirty w x)) ∧ ∀ cwd a c, M.Holds w' cwd a c ↔ M.Holds w cwd a c

/-! ### hc -/

/-- The terminals `hc ls --json` prints, as `Agents.hcTerminals` reads them: (address, state) of each. -/
def lsTerms (o : ProcOut) : Option (List (Option String × Option String)) :=
  let str (x : Json) (k : String) : Option String := (x.getObjValAs? String k).toOption
  match (Json.parse o.stdout).toOption with
  | none => none
  | some j => match j.getObjVal? "terminals" with
    | .ok (.arr ts) => some (ts.toList.map fun x => (str x "address", str x "state"))
    | .ok (.obj _) => some []
    | _ => none

/-- hc: when `hc ls --json` answers, it lists a terminal as live exactly when it is (when it does not answer the
code reads no list and reaps nothing) (env_spec: hc_ls_live). -/
def HcLsLive : Prop := ∀ w o ts h, M.out w ["hc", "ls", "--json"] none = some o → o.code = 0 → lsTerms o = some ts →
  ((some h, some "live") ∈ ts ↔ M.Live w h)

/-- hc: `hc kill h` ends terminal `h` and leaves the repo as it was (env_spec: hc_kill_ends). -/
def HcKillEnds : Prop := ∀ w h, ¬ M.Live (M.after w ["hc", "kill", h] none) h ∧ M.SameRepo w (M.after w ["hc", "kill", h] none)

/-- hc: `hc rm h` drops terminal `h`'s record and leaves the repo as it was (env_spec: hc_rm_keeps). -/
def HcRmKeeps : Prop := ∀ w h, M.SameRepo w (M.after w ["hc", "rm", h] none)

/-- hc: `hc send h l` to a live terminal types `l` into `h` and into no other terminal, starts or ends no terminal and
leaves the repo as it was (`swarm nudge`) (env_spec: hc_send_targets). -/
def HcSendTargets : Prop := ∀ w h l, M.Live w h →
  let w' := M.after w ["hc", "send", h, l] none
  M.typed w' h = M.typed w h ++ [l] ∧ (∀ h', h' ≠ h → M.typed w' h' = M.typed w h') ∧ (∀ h', M.Live w' h' ↔ M.Live w h') ∧
    M.SameRepo w w'

/-- hc: `hc run --json --bg …` that exits 0 started the program: the terminal whose address it prints is live and the
pid it prints runs (watchd's `--restart`) (env_spec: hc_run_starts). -/
def HcRunStarts : Prop := ∀ w rest o, M.out w (["hc", "run", "--json", "--bg"] ++ rest) none = some o → o.code = 0 →
  ∀ j, Json.parse o.stdout = .ok j →
  (∀ h, Json.fstr j "address" = some h → M.Live (M.after w (["hc", "run", "--json", "--bg"] ++ rest) none) h) ∧
  (∀ p, (j.getObjValAs? Int "pid").toOption = some p → M.Running (M.after w (["hc", "run", "--json", "--bg"] ++ rest) none) p)

/-! ### processes, files, the clock -/

/-- cgroups: writing "1" to a scope's `cgroup.kill` (`dir ++ "/cgroup.kill"`) kills what runs in it and leaves the repo
as it was (env_spec: cgroup_kill_keeps). -/
def CgroupKillKeeps : Prop := ∀ w dir, M.SameRepo w (M.effect w (.write (dir ++ "/cgroup.kill") "1"))

/-- processes: `kill(p, 0)` is 0 exactly when process `p` is in the process table, a zombie included (env_spec: kill0_alive). -/
def Kill0Alive : Prop := ∀ w p, M.pidAlive w p = true ↔ M.Running w p

/-- processes: `Machine.cwds`, when it answers, lists for every process inside a worktree a working directory whose
realpath (on the machine it left) is inside it (Linux: each /proc/<pid>/cwd; macOS: lsof) (env_spec: cwds_proc). -/
def CwdsProc : Prop := ∀ (s : Rec M) cs wt, (Rec.go Machine.cwds s).1 = .ok (some cs) → M.Inside s.w wt →
  ∃ c ∈ cs, Watchd.inside ((M.realpath (Rec.go Machine.cwds s).2.w c.2).getD c.2) wt = true

/-- filesystem: a worktree used in the last `SWEEP_IDLE` seconds reads as touched then: the later mtime of its directory
and of its git dir's `logs/HEAD` (`gd`, what `git rev-parse --absolute-git-dir` printed, stripped) is within that
(env_spec: touched_recent). -/
def TouchedRecent : Prop := ∀ w wt gd, M.Recent w wt → M.git w ["-C", wt, "rev-parse", "--absolute-git-dir"] none = some gd →
  M.now w - max ((M.mtime w wt).getD 0) ((M.mtime w (joinPath (joinPath ((py (some (strip gd))).getD wt) "logs") "HEAD")).getD 0)
    < Watchd.SWEEP_IDLE

/-- clock: `Clock.now` never goes back (a clock stepped back would read a lapsed lease live again) (env_spec: now_mono). -/
def NowMono : Prop := ∀ w w', M.Later w w' → M.now w ≤ M.now w'

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

/-- A machine on which no command runs and nothing is live, used, merged or later than anything. -/
def Tools.idle : Tools where
  World := Unit
  out _ _ _ := none
  git _ _ _ := none
  after w _ _ := w
  pidAlive _ _ := false
  mtime _ _ := none
  now _ := 0
  hhmm _ _ := ""
  var _ _ := none
  cwd _ := ""
  stdin _ := ""
  read _ _ := none
  list _ _ := none
  getpid _ := 0
  getppid _ := 0
  nowF _ := 0
  date _ _ _ := ""
  hostname _ := ""
  environ _ := []
  realpath _ _ := none
  readlink _ _ := none
  kind _ _ _ := .none
  launcherDir _ := none
  exec _ _ := ""
  run _ _ _ := ⟨127, "", ""⟩
  effect w _ := w
  ok _ _ := false
  rows _ _ := []
  Later _ _ := True
  Holds _ _ _ _ := False
  There _ _ := False
  Dirty _ _ := False
  tip _ _ := none
  Inside _ _ := False
  Recent _ _ := False
  Live _ _ := False
  Running _ _ := False
  typed _ _ := []
  checks _ _ := "pending"
  merged _ _ := false

/-- The tool assumptions hold together: the idle machine has them all. That the real tools have them is what
swarm-tests' env_spec cases test. -/
theorem consistent : AncestorReach .idle ∧ SameContentReach .idle ∧ StatusClean .idle ∧ ListedOn .idle ∧
    WtRemove .idle ∧ DelRef .idle ∧ HcLsLive .idle ∧ HcKillEnds .idle ∧ HcRmKeeps .idle ∧ HcSendTargets .idle ∧
    HcRunStarts .idle ∧ CgroupKillKeeps .idle ∧ Kill0Alive .idle ∧ CwdsProc .idle ∧ TouchedRecent .idle ∧
    NowMono .idle ∧ GhChecks .idle ∧ GhState .idle := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [AncestorReach, SameContentReach, StatusClean, ListedOn, WtRemove, DelRef, HcLsLive, HcKillEnds, HcRmKeeps,
      HcSendTargets, HcRunStarts, CgroupKillKeeps, Kill0Alive, CwdsProc, TouchedRecent, NowMono, GhChecks, GhState,
      Tools.idle, Tools.SameRepo, Ok0]

end SwarmLean
