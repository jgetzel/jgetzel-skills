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

/-- A primary-key integer cell (a rowid). -/
def Sqlite.Val.id : Val → Except String Nat
  | v => do match ← v.oi with
    | some i => pure i.toNat
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
  | «open» | claimed | blocked | done | dropped
  deriving DecidableEq, Repr, Inhabited

/-- The state's text in the db. -/
def Status.text : Status → String
  | .open => "open" | .claimed => "claimed" | .blocked => "blocked" | .done => "done" | .dropped => "dropped"

/-- The state a db text names. -/
def Status.ofText : String → Except String Status
  | "open" => .ok .open | "claimed" => .ok .claimed | "blocked" => .ok .blocked | "done" => .ok .done
  | "dropped" => .ok .dropped | s => .error s!"unknown task state '{s}'"

/-- One board task (table task). -/
structure Task where
  id : Nat
  title : Option String := none
  body : Option String := none
  state : Status := .open
  owner : Option String := none
  lease_until : Option Int := none
  created_by : Option String := none
  evidence : Option String := none
  deps : Option String := none
  model : Option String := none
  question : Option String := none
  effort : Option String := none
  created_at : Option Int := none
  first_claimed_at : Option Int := none
  done_at : Option Int := none
  dropped_at : Option Int := none
  pr : Option Int := none
  merged_at : Option Int := none
  ci_conclusion : Option String := none
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
  deriving DecidableEq, Repr, Inhabited

instance : Row Task where
  table := "task"
  cols := ["id", "title", "body", "state", "owner", "lease_until", "created_by", "evidence", "deps", "model", "question",
    "effort", "created_at", "first_claimed_at", "done_at", "dropped_at", "pr", "merged_at", "ci_conclusion",
    "ci_green_at", "claim_ctx", "done_ctx", "answer", "base", "stop_to", "stop_msg", "priority", "qpos", "hold"]
  nkey := 1
  enc t := [.int t.id, oS t.title, oS t.body, .text t.state.text, oS t.owner, oI t.lease_until, oS t.created_by,
    oS t.evidence, oS t.deps, oS t.model, oS t.question, oS t.effort, oI t.created_at, oI t.first_claimed_at,
    oI t.done_at, oI t.dropped_at, oI t.pr, oI t.merged_at, oS t.ci_conclusion, oI t.ci_green_at, oI t.claim_ctx,
    oI t.done_ctx, oS t.answer, oS t.base, oS t.stop_to, oI t.stop_msg, oI t.priority, oI t.qpos,
    oS t.hold]
  dec v := do
    let st ← match ← (col v 3).os with
      | some s => Status.ofText s
      | none => throw "NULL task state"
    pure { id := ← (col v 0).id, title := ← (col v 1).os, body := ← (col v 2).os, state := st,
           owner := ← (col v 4).os, lease_until := ← (col v 5).oi, created_by := ← (col v 6).os,
           evidence := ← (col v 7).os, deps := ← (col v 8).os, model := ← (col v 9).os, question := ← (col v 10).os,
           effort := ← (col v 11).os, created_at := ← (col v 12).oi, first_claimed_at := ← (col v 13).oi,
           done_at := ← (col v 14).oi, dropped_at := ← (col v 15).oi, pr := ← (col v 16).oi,
           merged_at := ← (col v 17).oi, ci_conclusion := ← (col v 18).os, ci_green_at := ← (col v 19).oi,
           claim_ctx := ← (col v 20).oi, done_ctx := ← (col v 21).oi, answer := ← (col v 22).os,
           base := ← (col v 23).os, stop_to := ← (col v 24).os, stop_msg := ← (col v 25).oi,
           priority := ← (col v 26).oi, qpos := ← (col v 27).oi, hold := ← (col v 28).os }

/-- One agent (table agent). -/
structure Agent where
  name : String
  hc : Option String := none
  model : Option String := none
  cwd : Option String := none
  status : Option String := none
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
  enc a := [.text a.name, oS a.hc, oS a.model, oS a.cwd, oS a.status, oI a.last_active, oI a.ctx_tokens,
    oI a.compacted_at, oI a.started, oI a.ended, oS a.snap, oI a.waiter, oS a.wt, oI a.claude_pid, oS a.role, oS a.stay]
  dec v := do
    pure { name := ← (col v 0).key, hc := ← (col v 1).os, model := ← (col v 2).os, cwd := ← (col v 3).os,
           status := ← (col v 4).os, last_active := ← (col v 5).oi, ctx_tokens := ← (col v 6).oi,
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

/-- A path lock (table lock). -/
structure Lock where
  path : String
  agent : Option String := none
  reason : Option String := none
  since : Option Int := none
  lease_until : Option Int := none
  seen : Option Int := some 0
  deriving DecidableEq, Repr, Inhabited

instance : Row Lock where
  table := "lock"
  cols := ["path", "agent", "reason", "since", "lease_until", "seen"]
  nkey := 1
  enc l := [.text l.path, oS l.agent, oS l.reason, oI l.since, oI l.lease_until, oI l.seen]
  dec v := do
    pure { path := ← (col v 0).key, agent := ← (col v 1).os, reason := ← (col v 2).os, since := ← (col v 3).oi,
           lease_until := ← (col v 4).oi, seen := ← (col v 5).oi }

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

/-- A swarm worktree and who works in it (table workspace). -/
structure Workspace where
  path : String
  agent : String
  branch : Option String := none
  base : Option String := none
  ro : Option Int := some 0
  deriving DecidableEq, Repr, Inhabited

instance : Row Workspace where
  table := "workspace"
  cols := ["path", "agent", "branch", "base", "ro"]
  nkey := 2
  enc w := [.text w.path, .text w.agent, oS w.branch, oS w.base, oI w.ro]
  dec v := do
    pure { path := ← (col v 0).key, agent := ← (col v 1).key, branch := ← (col v 2).os, base := ← (col v 3).os,
           ro := ← (col v 4).oi }

/-- One CI run watchd polled (table ci). -/
structure Ci where
  id : Nat
  sha : Option String := none
  status : Option String := none
  conclusion : Option String := none
  url : Option String := none
  created : Option String := none
  updated : Option String := none
  failed : Option String := none
  workflow : Option String := none
  deriving DecidableEq, Repr, Inhabited

instance : Row Ci where
  table := "ci"
  cols := ["id", "sha", "status", "conclusion", "url", "created", "updated", "failed", "workflow"]
  nkey := 1
  enc c := [.int c.id, oS c.sha, oS c.status, oS c.conclusion, oS c.url, oS c.created, oS c.updated, oS c.failed,
    oS c.workflow]
  dec v := do
    pure { id := ← (col v 0).id, sha := ← (col v 1).os, status := ← (col v 2).os, conclusion := ← (col v 3).os,
           url := ← (col v 4).os, created := ← (col v 5).os, updated := ← (col v 6).os, failed := ← (col v 7).os,
           workflow := ← (col v 8).os }

end SwarmLean
