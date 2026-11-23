import SwarmLean.Sqlite
import SwarmLean.Util

/-! One structure per table of swarm/lua/swarm/db.lua's schema (with its COLUMNS migrations), fields named as the
columns; every column but the primary key is optional, as SQLite allows NULL in each. -/

namespace SwarmLean
open Sqlite (Val)

/-- A cell as optional text: NULL is none; a number is its text, as SQLite's text affinity stores it. -/
def Sqlite.Val.os : Val → Except String (Option String)
  | .null => .ok none
  | .text s => .ok (some s)
  | .int i => .ok (some (toString i))
  | .real f => .ok (some (toString f))

/-- A cell as an optional integer: NULL is none; integral text or float is the integer. -/
def Sqlite.Val.oi : Val → Except String (Option Int)
  | .null => .ok none
  | .int i => .ok (some i)
  | .text s => match parseInt s with
    | some i => .ok (some i)
    | none => .error s!"not an integer: '{s}'"
  | .real f => if f == f.floor && f.abs < 9.0e15 then .ok (some f.toInt64.toInt) else .error s!"not an integer: {f}"

/-- A primary-key text cell. -/
def Sqlite.Val.key : Val → Except String String
  | v => do match ← v.os with
    | some s => pure s
    | none => throw "NULL in a primary key"

/-- A primary-key integer cell (a rowid); a negative one is refused, not read as 0. -/
def Sqlite.Val.id : Val → Except String Nat
  | v => do match ← v.oi with
    | some (.ofNat n) => pure n
    | some i => throw s!"negative id {i}"
    | none => throw "NULL id"

/-- An optional text as a cell. -/
def oS : Option String → Val
  | some s => .text s
  | none => .null

/-- An optional integer as a cell. -/
def oI : Option Int → Val
  | some i => .int i
  | none => .null

/-- How a row type maps to its table: the columns (key columns first), and the codec. -/
class Row (α : Type) where
  table : String
  cols : List String
  nkey : Nat
  enc : α → List Val
  dec : Array Val → Except String α

/-- The value of column `i`. -/
def col (v : Array Val) (i : Nat) : Val := v.getD i .null

/-- Where a task is in its life (task.state). -/
inductive Status
  | «open» | claimed | blocked | done | dropped | landing
  deriving DecidableEq, Repr, Inhabited

/-- The state's text in the db. -/
def Status.text : Status → String
  | .open => "open" | .claimed => "claimed" | .blocked => "blocked" | .done => "done" | .dropped => "dropped"
  | .landing => "landing"

/-- The state a db text names. -/
def Status.ofText : String → Except String Status
  | "open" => .ok .open | "claimed" => .ok .claimed | "blocked" => .ok .blocked | "done" => .ok .done
  | "dropped" => .ok .dropped | "landing" => .ok .landing | s => .error s!"unknown task state '{s}'"

/-- A CI run's status as GitHub sends it (text in the db and in gh's REST JSON; gh's CLI upper-cases it). -/
inductive RunStatus
  | queued | inProgress | completed | waiting | requested | pending
  | other (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- The status's text. -/
def RunStatus.text : RunStatus → String
  | .queued => "queued" | .inProgress => "in_progress" | .completed => "completed" | .waiting => "waiting"
  | .requested => "requested" | .pending => "pending" | .other s => s

/-- The status a text names; a value GitHub adds later keeps its text. -/
def RunStatus.ofText : String → RunStatus
  | "queued" => .queued | "in_progress" => .inProgress | "completed" => .completed | "waiting" => .waiting
  | "requested" => .requested | "pending" => .pending | s => .other s

/-- The status of gh's CLI text (COMPLETED, IN_PROGRESS, …). -/
def RunStatus.ofGh (s : String) : RunStatus := match RunStatus.ofText s.toLower with
  | .other _ => .other s
  | k => k

/-- A CI run's conclusion as GitHub sends it. -/
inductive Conclusion
  | success | failure | neutral | cancelled | skipped | timedOut | actionRequired | startupFailure | stale
  | other (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- The conclusion's text. -/
def Conclusion.text : Conclusion → String
  | .success => "success" | .failure => "failure" | .neutral => "neutral" | .cancelled => "cancelled"
  | .skipped => "skipped" | .timedOut => "timed_out" | .actionRequired => "action_required"
  | .startupFailure => "startup_failure" | .stale => "stale" | .other s => s

/-- The conclusion a text names; a value GitHub adds later keeps its text. -/
def Conclusion.ofText : String → Conclusion
  | "success" => .success | "failure" => .failure | "neutral" => .neutral | "cancelled" => .cancelled
  | "skipped" => .skipped | "timed_out" => .timedOut | "action_required" => .actionRequired
  | "startup_failure" => .startupFailure | "stale" => .stale | s => .other s

/-- The conclusion of gh's CLI text (SUCCESS, TIMED_OUT, …). -/
def Conclusion.ofGh (s : String) : Conclusion := match Conclusion.ofText s.toLower with
  | .other _ => .other s
  | k => k

/-- Finished without failing the way a check may not: what a PR's rollup counts green. -/
def Conclusion.passes : Conclusion → Bool
  | .success | .neutral | .skipped => true
  | _ => false

/-- A hand-over to a lander (`task land`, board #200): the commit, the lander it named (none: any lander), when. -/
structure Landing where
  sha : String
  lander : Option String := none
  since : Int
  deriving DecidableEq, Repr, Inhabited

/-- Where a task is in its life, with what that state holds: the owner of a claim (claimed, blocked, landing), its
lease, a block's question, a hand-over to a lander. A done task keeps the owner, question and hand-over it had; a
dropped one the question and hand-over (`drop` and the green run's close take a task as it is). -/
inductive TaskState
  | «open»
  | claimed (owner : String) (lease : Int)
  | blocked (owner : String) (lease : Int) (question : String)
  | landing (owner : String) (hand : Landing)
  | done (owner : Option String) (question : Option String) (hand : Option Landing)
  | dropped (question : Option String) (hand : Option Landing)
  deriving DecidableEq, Repr, Inhabited

namespace TaskState

/-- The state's name. -/
def status : TaskState → Status
  | .open => .open | .claimed .. => .claimed | .blocked .. => .blocked | .landing .. => .landing | .done .. => .done
  | .dropped .. => .dropped

/-- The owner (column owner). -/
def owner : TaskState → Option String
  | .claimed o _ | .blocked o _ _ | .landing o _ => some o
  | .done o _ _ => o
  | _ => none

/-- The claim's lease (column lease_until). -/
def lease : TaskState → Option Int
  | .claimed _ l | .blocked _ l _ => some l
  | _ => none

/-- The block's question (column question). -/
def question : TaskState → Option String
  | .blocked _ _ q => some q
  | .done _ q _ | .dropped q _ => q
  | _ => none

/-- The hand-over to a lander (columns land_sha, lander, landing_at). -/
def hand : TaskState → Option Landing
  | .landing _ h => some h
  | .done _ _ h | .dropped _ h => h
  | _ => none

/-- Closed as done: the owner, question and hand-over kept. -/
def toDone (s : TaskState) : TaskState := .done s.owner s.question s.hand

/-- Dropped: the question and hand-over kept. -/
def toDropped (s : TaskState) : TaskState := .dropped s.question s.hand

/-- A claim's lease moved to `u`; any other state as it is. -/
def renew (u : Int) : TaskState → TaskState
  | .claimed o _ => .claimed o u
  | s => s

/-- A claim blocked on question `q`, its lease kept; any other state as it is. -/
def block (q : String) : TaskState → TaskState
  | .claimed o l => .blocked o l q
  | s => s

/-- A block answered: claimed again by its owner until `u`; any other state as it is. -/
def unblock (u : Int) : TaskState → TaskState
  | .blocked o _ _ => .claimed o u
  | s => s

/-- The hand-over's columns. -/
def handCols : Option Landing → Option String × Option String × Option Int
  | some h => (some h.sha, h.lander, some h.since)
  | none => (none, none, none)

/-- The hand-over the columns land_sha, lander, landing_at hold: all NULL is none, a commit and a time is one. -/
def handOf : Option String × Option String × Option Int → Option (Option Landing)
  | (none, none, none) => some none
  | (some s, l, some t) => some (some ⟨s, l, t⟩)
  | _ => none

/-- The columns a state of status `s` must have set, and those it may: owner, lease_until, question, land_sha,
landing_at, lander. -/
def colsOf : Status → List String × List String
  | .open => ([], [])
  | .claimed => (["owner", "lease_until"], [])
  | .blocked => (["owner", "lease_until", "question"], [])
  | .landing => (["owner", "land_sha", "landing_at"], ["lander"])
  | .done => ([], ["owner", "question", "land_sha", "landing_at", "lander"])
  | .dropped => ([], ["question", "land_sha", "landing_at", "lander"])

/-- Why columns `set` (the names of the non-NULL ones) fit no state of status `s`. -/
def misfit (s : Status) (set : List String) : String :=
  let (need, may) := colsOf s
  let need := if (set.any (["land_sha", "landing_at", "lander"].contains ·)) && may.contains "land_sha" then
    need ++ ["land_sha", "landing_at"] else need
  let missing := need.filter (!set.contains ·)
  let extra := set.filter fun c => !need.contains c && !may.contains c
  let w := if missing.isEmpty then "" else s!" with no {", ".intercalate missing}"
  let x := if extra.isEmpty then "" else s!"{if missing.isEmpty then " with" else " and"} {", ".intercalate extra} set"
  s!"{s.text}{if w ++ x == "" then " with columns that fit no state" else w ++ x}"

/-- The state the columns state, owner, lease_until, question, land_sha, lander, landing_at hold; the refusal names
what a row that fits no state lacks or holds. -/
def ofCols (s : Status) (owner : Option String) (lease : Option Int) (question : Option String)
    (sha lander : Option String) (at_ : Option Int) : Except String TaskState :=
  match s, owner, lease, question, handOf (sha, lander, at_) with
  | .open, none, none, none, some none => .ok .open
  | .claimed, some o, some l, none, some none => .ok (.claimed o l)
  | .blocked, some o, some l, some q, some none => .ok (.blocked o l q)
  | .landing, some o, none, none, some (some h) => .ok (.landing o h)
  | .done, o, none, q, some h => .ok (.done o q h)
  | .dropped, none, none, q, some h => .ok (.dropped q h)
  | _, _, _, _, _ =>
    .error (misfit s ([("owner", owner.isSome), ("lease_until", lease.isSome), ("question", question.isSome),
      ("land_sha", sha.isSome), ("landing_at", at_.isSome), ("lander", lander.isSome)].filterMap
        fun (c, b) => if b then some c else none))

theorem handOf_handCols (h : Option Landing) : handOf (handCols h) = some h := by
  cases h <;> rfl

theorem handCols_handOf {c : Option String × Option String × Option Int} {h : Option Landing}
    (e : handOf c = some h) : handCols h = c := by
  match c, e with
  | (none, none, none), e => cases e; rfl
  | (some _, _, some _), e => cases e; rfl

/-- Every state decodes from its own columns. -/
theorem ofCols_self (t : TaskState) :
    ofCols t.status t.owner t.lease t.question (handCols t.hand).1 (handCols t.hand).2.1 (handCols t.hand).2.2 =
      .ok t := by
  cases t with
  | «open» => rfl
  | claimed => rfl
  | blocked => rfl
  | landing o h => rfl
  | done o q h => cases h <;> rfl
  | dropped q h => cases h <;> rfl

/-- What decodes writes back the same columns: a row that is read and written is unchanged. -/
theorem ofCols_cols {s : Status} {o : Option String} {l : Option Int} {q sha ld : Option String} {at_ : Option Int}
    {t : TaskState} (e : ofCols s o l q sha ld at_ = .ok t) :
    t.status = s ∧ t.owner = o ∧ t.lease = l ∧ t.question = q ∧ handCols t.hand = (sha, ld, at_) := by
  unfold ofCols at e
  split at e <;> (try cases e) <;> rename_i hh <;> simp [status, owner, lease, question, hand, handCols_handOf hh]

/-- A claimed task has an owner and an open one none (`Task.Owned`): by construction. -/
theorem owned (t : TaskState) : (t.status = .claimed → t.owner.isSome) ∧ (t.status = .open → t.owner = none) := by
  cases t <;> simp [status, owner]

end TaskState

/-- One board task (table task). -/
structure Task where
  id : Nat
  title : Option String := none
  body : Option String := none
  state : TaskState := .open
  created_by : Option String := none
  evidence : Option String := none
  deps : Option String := none
  model : Option String := none
  effort : Option String := none
  created_at : Option Int := none
  first_claimed_at : Option Int := none
  done_at : Option Int := none
  dropped_at : Option Int := none
  pr : Option Int := none
  merged_at : Option Int := none
  ci_conclusion : Option Conclusion := none
  ci_green_at : Option Int := none
  claim_ctx : Option Int := none
  done_ctx : Option Int := none
  answer : Option String := none
  base : Option String := none
  stop_to : Option String := none
  stop_msg : Option Int := none
  priority : Option Int := some 2
  /-- the task's place in the staffing queue, 1..n (board #128); none: not queued -/
  qpos : Option Int := none
  /-- why the task is held from staffing (board #128); none: not held -/
  hold : Option String := none
  /-- its labels, comma-separated (board #186) -/
  labels : Option String := none
  /-- the tasks its creator held when it was added, comma-separated ids (board #186) -/
  parents : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- The task's state's name. -/
def Task.status (t : Task) : Status := t.state.status
/-- Its owner: the claim's holder, or who a done task was done by. -/
def Task.owner (t : Task) : Option String := t.state.owner
/-- Its claim's lease. -/
def Task.lease_until (t : Task) : Option Int := t.state.lease
/-- Its block's question. -/
def Task.question (t : Task) : Option String := t.state.question
/-- The commit its owner handed to a lander (`task land`, board #200). -/
def Task.land_sha (t : Task) : Option String := t.state.hand.map (·.sha)
/-- The lander `task land --lander` named. -/
def Task.lander (t : Task) : Option String := t.state.hand.bind (·.lander)
/-- When it was handed to a lander. -/
def Task.landing_at (t : Task) : Option Int := t.state.hand.map (·.since)

instance : Row Task where
  table := "task"
  cols := ["id", "title", "body", "state", "owner", "lease_until", "created_by", "evidence", "deps", "model", "question",
    "effort", "created_at", "first_claimed_at", "done_at", "dropped_at", "pr", "merged_at", "ci_conclusion",
    "ci_green_at", "claim_ctx", "done_ctx", "answer", "base", "stop_to", "stop_msg", "priority", "qpos", "hold",
    "labels", "parents", "land_sha", "lander", "landing_at"]
  nkey := 1
  enc t := [.int t.id, oS t.title, oS t.body, .text t.status.text, oS t.owner, oI t.lease_until, oS t.created_by,
    oS t.evidence, oS t.deps, oS t.model, oS t.question, oS t.effort, oI t.created_at, oI t.first_claimed_at,
    oI t.done_at, oI t.dropped_at, oI t.pr, oI t.merged_at, oS (t.ci_conclusion.map Conclusion.text), oI t.ci_green_at, oI t.claim_ctx,
    oI t.done_ctx, oS t.answer, oS t.base, oS t.stop_to, oI t.stop_msg, oI t.priority, oI t.qpos,
    oS t.hold, oS t.labels, oS t.parents, oS t.land_sha, oS t.lander, oI t.landing_at]
  dec v := do
    let st ← match ← (col v 3).os with
      | some s => Status.ofText s
      | none => throw "NULL task state"
    let st ← TaskState.ofCols st (← (col v 4).os) (← (col v 5).oi) (← (col v 10).os) (← (col v 31).os) (← (col v 32).os)
      (← (col v 33).oi)
    pure { id := ← (col v 0).id, title := ← (col v 1).os, body := ← (col v 2).os, state := st,
           created_by := ← (col v 6).os,
           evidence := ← (col v 7).os, deps := ← (col v 8).os, model := ← (col v 9).os,
           effort := ← (col v 11).os, created_at := ← (col v 12).oi, first_claimed_at := ← (col v 13).oi,
           done_at := ← (col v 14).oi, dropped_at := ← (col v 15).oi, pr := ← (col v 16).oi,
           merged_at := ← (col v 17).oi, ci_conclusion := (← (col v 18).os).map Conclusion.ofText, ci_green_at := ← (col v 19).oi,
           claim_ctx := ← (col v 20).oi, done_ctx := ← (col v 21).oi, answer := ← (col v 22).os,
           base := ← (col v 23).os, stop_to := ← (col v 24).os, stop_msg := ← (col v 25).oi,
           priority := ← (col v 26).oi, qpos := ← (col v 27).oi, hold := ← (col v 28).os,
           labels := ← (col v 29).os, parents := ← (col v 30).os }

/-- An agent row's status in the db. -/
inductive AgentStatus
  | idle | working | blocked | ended
  deriving DecidableEq, Repr, Inhabited

/-- The status's text in the db. -/
def AgentStatus.text : AgentStatus → String
  | .idle => "idle" | .working => "working" | .blocked => "blocked" | .ended => "ended"

/-- The status a db text names. -/
def AgentStatus.ofText : String → Except String AgentStatus
  | "idle" => .ok .idle | "working" => .ok .working | "blocked" => .ok .blocked | "ended" => .ok .ended
  | s => .error s!"unknown agent status '{s}'"

/-- One agent (table agent). -/
structure Agent where
  name : String
  hc : Option String := none
  model : Option String := none
  cwd : Option String := none
  status : Option AgentStatus := none
  last_active : Option Int := none
  ctx_tokens : Option Int := some 0
  compacted_at : Option Int := some 0
  started : Option Int := none
  ended : Option Int := none
  snap : Option String := none
  waiter : Option Int := none
  wt : Option String := none
  claude_pid : Option Int := none
  role : Option String := none
  stay : Option String := none
  deriving DecidableEq, Repr, Inhabited

instance : Row Agent where
  table := "agent"
  cols := ["name", "hc", "model", "cwd", "status", "last_active", "ctx_tokens", "compacted_at", "started", "ended", "snap",
    "waiter", "wt", "claude_pid", "role", "stay"]
  nkey := 1
  enc a := [.text a.name, oS a.hc, oS a.model, oS a.cwd, oS (a.status.map (·.text)), oI a.last_active, oI a.ctx_tokens,
    oI a.compacted_at, oI a.started, oI a.ended, oS a.snap, oI a.waiter, oS a.wt, oI a.claude_pid, oS a.role, oS a.stay]
  dec v := do
    pure { name := ← (col v 0).key, hc := ← (col v 1).os, model := ← (col v 2).os, cwd := ← (col v 3).os,
           status := ← (← (col v 4).os).mapM AgentStatus.ofText, last_active := ← (col v 5).oi, ctx_tokens := ← (col v 6).oi,
           compacted_at := ← (col v 7).oi, started := ← (col v 8).oi, ended := ← (col v 9).oi,
           snap := ← (col v 10).os, waiter := ← (col v 11).oi, wt := ← (col v 12).os, claude_pid := ← (col v 13).oi,
           role := ← (col v 14).os, stay := ← (col v 15).os }

/-- One message (table msg). -/
structure Msg where
  id : Nat
  ts : Option Int := none
  frm : Option String := none
  dest : Option String := none
  body : Option String := none
  urgent : Option Int := some 0
  kind : Option String := none
  deriving DecidableEq, Repr, Inhabited

instance : Row Msg where
  table := "msg"
  cols := ["id", "ts", "frm", "dest", "body", "urgent", "kind"]
  nkey := 1
  enc m := [.int m.id, oI m.ts, oS m.frm, oS m.dest, oS m.body, oI m.urgent, oS m.kind]
  dec v := do
    pure { id := ← (col v 0).id, ts := ← (col v 1).oi, frm := ← (col v 2).os, dest := ← (col v 3).os,
           body := ← (col v 4).os, urgent := ← (col v 5).oi, kind := ← (col v 6).os }

/-- How far an agent has read its messages (table cursor). -/
structure Cursor where
  agent : String
  last_msg_id : Option Int := some 0
  deriving DecidableEq, Repr, Inhabited

instance : Row Cursor where
  table := "cursor"
  cols := ["agent", "last_msg_id"]
  nkey := 1
  enc c := [.text c.agent, oI c.last_msg_id]
  dec v := do pure { agent := ← (col v 0).key, last_msg_id := ← (col v 1).oi }

/-- A path lock (table lock): keyed by its repo (the main worktree's toplevel) and the path relative to it. -/
structure Lock where
  repo : String := ""
  path : String
  agent : Option String := none
  reason : Option String := none
  since : Option Int := none
  lease_until : Option Int := none
  seen : Option Int := some 0
  deriving DecidableEq, Repr, Inhabited

instance : Row Lock where
  table := "lock"
  cols := ["repo", "path", "agent", "reason", "since", "lease_until", "seen"]
  nkey := 2
  enc l := [.text l.repo, .text l.path, oS l.agent, oS l.reason, oI l.since, oI l.lease_until, oI l.seen]
  dec v := do
    pure { repo := ← (col v 0).key, path := ← (col v 1).key, agent := ← (col v 2).os, reason := ← (col v 3).os,
           since := ← (col v 4).oi, lease_until := ← (col v 5).oi, seen := ← (col v 6).oi }

/-- A conflict notice between two agents on a path (table conflict). -/
structure Conflict where
  a : String
  b : String
  path : String
  since : Option Int := none
  deriving DecidableEq, Repr, Inhabited

instance : Row Conflict where
  table := "conflict"
  cols := ["a", "b", "path", "since"]
  nkey := 3
  enc c := [.text c.a, .text c.b, .text c.path, oI c.since]
  dec v := do pure { a := ← (col v 0).key, b := ← (col v 1).key, path := ← (col v 2).key, since := ← (col v 3).oi }

/-- The last conflict state seen for a pair of agents (table pairkey). -/
structure Pairkey where
  a : String
  b : String
  key : Option String := none
  deriving DecidableEq, Repr, Inhabited

instance : Row Pairkey where
  table := "pairkey"
  cols := ["a", "b", "key"]
  nkey := 2
  enc p := [.text p.a, .text p.b, oS p.key]
  dec v := do pure { a := ← (col v 0).key, b := ← (col v 1).key, key := ← (col v 2).os }

/-- A key-value setting (table meta). -/
structure Meta where
  k : String
  v : Option String := none
  deriving DecidableEq, Repr, Inhabited

instance : Row Meta where
  table := "meta"
  cols := ["k", "v"]
  nkey := 1
  enc m := [.text m.k, oS m.v]
  dec v := do pure { k := ← (col v 0).key, v := ← (col v 1).os }

/-- One line of the event log (table event). -/
structure Event where
  id : Nat
  ts : Option Int := none
  agent : Option String := none
  kind : Option String := none
  path : Option String := none
  data : Option String := none
  deriving DecidableEq, Repr, Inhabited

instance : Row Event where
  table := "event"
  cols := ["id", "ts", "agent", "kind", "path", "data"]
  nkey := 1
  enc e := [.int e.id, oI e.ts, oS e.agent, oS e.kind, oS e.path, oS e.data]
  dec v := do
    pure { id := ← (col v 0).id, ts := ← (col v 1).oi, agent := ← (col v 2).os, kind := ← (col v 3).os,
           path := ← (col v 4).os, data := ← (col v 5).os }

/-- A swarm worktree, who works in it and the repo it is a worktree of (table workspace). -/
structure Workspace where
  path : String
  agent : String
  branch : Option String := none
  base : Option String := none
  ro : Option Int := some 0
  /-- the main worktree of its repo; `''` when not known -/
  repo : String := ""
  deriving DecidableEq, Repr, Inhabited

instance : Row Workspace where
  table := "workspace"
  cols := ["path", "agent", "branch", "base", "ro", "repo"]
  nkey := 2
  enc w := [.text w.path, .text w.agent, oS w.branch, oS w.base, oI w.ro, .text w.repo]
  dec v := do
    pure { path := ← (col v 0).key, agent := ← (col v 1).key, branch := ← (col v 2).os, base := ← (col v 3).os,
           ro := ← (col v 4).oi, repo := ← (col v 5).key }

/-- One CI run watchd polled (table ci). -/
structure Ci where
  id : Nat
  sha : Option String := none
  status : Option RunStatus := none
  conclusion : Option Conclusion := none
  url : Option String := none
  created : Option String := none
  updated : Option String := none
  failed : Option String := none
  workflow : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- A run that finished and was not cancelled. -/
def Ci.finished (c : Ci) : Bool := c.status == some .completed && c.conclusion.any (· != .cancelled)

instance : Row Ci where
  table := "ci"
  cols := ["id", "sha", "status", "conclusion", "url", "created", "updated", "failed", "workflow"]
  nkey := 1
  enc c := [.int c.id, oS c.sha, oS (c.status.map RunStatus.text), oS (c.conclusion.map Conclusion.text), oS c.url, oS c.created, oS c.updated, oS c.failed,
    oS c.workflow]
  dec v := do
    pure { id := ← (col v 0).id, sha := ← (col v 1).os, status := (← (col v 2).os).map RunStatus.ofText, conclusion := (← (col v 3).os).map Conclusion.ofText,
           url := ← (col v 4).os, created := ← (col v 5).os, updated := ← (col v 6).os, failed := ← (col v 7).os,
           workflow := ← (col v 8).os }

end SwarmLean
